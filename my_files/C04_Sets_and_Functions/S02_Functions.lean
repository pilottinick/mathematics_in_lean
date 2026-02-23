import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  . intro hf x xin
    apply hf
    use x
  . rintro hf _ ⟨x, ⟨xin, rfl⟩⟩
    use hf xin

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro x ⟨y, ⟨yin, fy_eq_fx⟩⟩
  rw [← h fy_eq_fx]
  assumption

example : f '' (f ⁻¹' u) ⊆ u := by
  rintro y ⟨x, ⟨xin, rfl⟩⟩
  assumption

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y yin
  rcases h y with ⟨x, ⟨xin, rfl⟩⟩
  use x, yin

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  rintro y ⟨x, ⟨xin, rfl⟩⟩
  use x, h xin

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x xin
  exact h xin

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  dsimp

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro y ⟨x, ⟨xin, rfl⟩⟩
  constructor
  use x, xin.1
  use x, xin.2

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro y ⟨⟨x₁, ⟨x₁s, x₁eq⟩⟩, ⟨x₂, ⟨x₂t, x₂eq ⟩⟩⟩
  have fx₁eqfx₂ : f x₁ = f x₂ := by rw [x₁eq, x₂eq]
  have x₁t : x₁ ∈ t := by rw [h fx₁eqfx₂] ; exact x₂t
  exact ⟨x₁, ⟨⟨x₁s, x₁t⟩, x₁eq⟩⟩

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro y ⟨⟨x, ⟨xs, rfl⟩⟩, ynt⟩
  have xnt : x ∉ t := by intro xt ; exact ynt ⟨x, ⟨xt, rfl⟩⟩
  exact ⟨x, ⟨⟨xs, xnt⟩, rfl⟩⟩

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  rintro _ h ; exact h

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y ; constructor
  . rintro ⟨⟨x, ⟨xs, rfl⟩⟩, xv⟩
    exact ⟨x, ⟨⟨xs, xv⟩, rfl⟩⟩
  . rintro ⟨x, ⟨⟨xs, xv⟩, rfl⟩⟩
    exact ⟨⟨x, ⟨xs, rfl⟩⟩, xv⟩

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  intro y ⟨x, ⟨xs, xu⟩⟩ ; rw [← xu]
  exact ⟨⟨x, ⟨xs.1, rfl⟩⟩, xs.2⟩

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  intro x ⟨xs, xu⟩
  exact ⟨⟨x, ⟨xs, rfl⟩⟩, xu⟩

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs | xu)
  . exact Or.inl ⟨x, ⟨xs, rfl⟩⟩
  . exact Or.inr xu

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y ;  simp ; constructor
  . rintro ⟨x, ⟨⟨i, xin⟩, fxeqy⟩⟩
    exact ⟨i, x, xin, fxeqy⟩
  . rintro ⟨i, x, xin, fxeqy⟩
    exact ⟨x, ⟨⟨i, xin⟩, fxeqy⟩⟩

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro y ⟨x, ⟨xin, fxeqy⟩⟩ ; simp at *
  intro i
  use x, xin i, fxeqy


example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y yin ; simp at *
  rcases yin i with ⟨x, hx⟩
  use x
  constructor
  . intro i₀
    rcases yin i₀ with ⟨x₀, hx₀⟩
    have hfxeqfx₀ : f x = f x₀ := by
      rw [hx.2, hx₀.2]
    rw [injf hfxeqfx₀]
    exact hx₀.1
  . exact hx.2

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x ; simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xnn y ynn
  intro e
  calc
    x = √x ^ 2 := by rw [sq_sqrt xnn]
    _ = √y ^ 2 := by rw [e]
    _ = y := by rw [sq_sqrt ynn]

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xnn y ynn
  intro e ; dsimp at e
  calc
    x = √(x ^ 2) := by rw [sqrt_sq xnn]
    _ = √(y ^ 2) := by rw [e]
    _ = y := by rw [sqrt_sq ynn]

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y ; constructor
  . rintro ⟨x, ⟨xin, rfl⟩⟩
    apply sqrt_nonneg
  intro ynn
  exact ⟨y^2, ⟨sq_nonneg y, sqrt_sq ynn⟩⟩

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y ; simp ; constructor
  . rintro ⟨z, rfl⟩
    apply sq_nonneg z
  . intro ynn
    exact ⟨√y, sq_sqrt ynn⟩

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  . exact fun injf x => injf (inverse_spec (f x) ⟨x, rfl⟩)
  . intro invf x y fxeqfy
    calc
      x = inverse f (f x) := by rw [invf]
      _ = inverse f (f y) := by rw [fxeqfy]
      _ = y := by rw [invf]

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  . intro fsurj y
    rcases fsurj y with ⟨x, ⟨xin, rfl⟩⟩
    rw [inverse_spec (f x) ⟨x, rfl⟩]
  . intro finv y
    exact ⟨(inverse f) y, finv y⟩

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := h₁
  rw [← h] at h₂
  contradiction

-- COMMENTS: TODO: improve this
lemma aux (P : Prop) : ¬(P ↔ ¬P) := by
  intro h
  have np : ¬P := fun hp => (h.mp hp) hp
  exact np (h.mpr np)

theorem Cantor2 : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have c : j ∈ f j ↔ j ∉ f j := by
    nth_rw 1 [h]
    rfl
  exact aux _ c

end
