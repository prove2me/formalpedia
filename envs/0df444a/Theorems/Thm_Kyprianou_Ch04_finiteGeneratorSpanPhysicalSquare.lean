-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteGeneratorSpanPhysicalSquare
-- name    : Kyprianou.Ch04.finiteGeneratorSpanPhysicalSquare
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:23:52.716343+00:00
-- url     : https://prove2.me/theorems/ab9184b4-0fef-4e71-9eaa-69b16c366128
-- title:
--   finiteGeneratorSpanPhysicalSquare
-- statement:
--   The physical square-integral identity on finite pointwise generator sums transfers to their L2 equivalence classes.
-- source:
--   Kyprianou (2006), Exercise 4.4, dense physical L2 extension.

import Mathlib
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators
set_option autoImplicit false

/-- Physical square identities pass from pointwise generator sums to their L2 classes. -/
theorem Kyprianou.Ch04.finiteGeneratorSpanPhysicalSquare
    {A Omega : Type} [MeasurableSpace A] [MeasurableSpace Omega]
    (mu : Measure A) [IsFiniteMeasure mu] (P : Measure Omega)
    (G : Set (Set A)) (T : (A → ℝ) → Omega → ℝ)
    (hT : ∀ f g : A → ℝ, Measurable f → Measurable g →
      Integrable f mu → Integrable g mu →
      Integrable (T f) P ∧ Integrable (T g) P ∧
        (∫ w, |T f w - T g w| ∂P) ≤ 2 * ∫ a, |f a - g a| ∂mu)
    (hSimple : ∀ (k : ℕ) (D : Fin k → Set A) (c : Fin k → ℝ),
      (∀ i, D i ∈ G) →
      let f : A → ℝ := fun a => ∑ i, c i * (D i).indicator (fun _ => (1 : ℝ)) a
      Measurable f → MemLp f 2 mu →
      Integrable (fun w => (T f w)^2) P ∧
        (∫ w, (T f w)^2 ∂P) = ∫ a, (f a)^2 ∂mu)
    (v : Lp ℝ 2 mu)
    (hv : v ∈ Submodule.span ℝ
      {w : Lp ℝ 2 mu | ∃ (B : Set A), B ∈ G ∧
        ∃ (hB : MeasurableSet B) (hfin : mu B ≠ ⊤),
          indicatorConstLp 2 hB hfin (1 : ℝ) = w}) :
    Integrable (fun w => (T (v : A → ℝ) w)^2) P ∧
      (∫ w, (T (v : A → ℝ) w)^2 ∂P) = ∫ a, (v a)^2 ∂mu := by
  sorry
