-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exhaustedPhysicalL2Isometry
-- name    : Kyprianou.Ch04.exhaustedPhysicalL2Isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:36:54.37194+00:00
-- url     : https://prove2.me/theorems/2149eefb-5a09-4f88-880e-d481ffef3881
-- title:
--   Physical L2 isometry by exhaustion
-- statement:
--   The exact physical L2 isometry on an increasing measurable exhaustion extends to every L1 and L2 kernel under the L1 continuity and subtraction properties.
-- source:
--   Kyprianou (2006), Exercise 4.4, mark-band exhaustion

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

/-- Extend a physical isometry on finite bands to every integrable L2 kernel. -/
theorem Kyprianou.Ch04.exhaustedPhysicalL2Isometry {A Omega : Type} [MeasurableSpace A] [MeasurableSpace Omega]
    (mu : Measure A) (P : Measure Omega) (T : (A → ℝ) → Omega → ℝ)
    (hT : ∀ f g : A → ℝ, Measurable f → Measurable g →
      Integrable f mu → Integrable g mu →
      Integrable (T f) P ∧ Integrable (T g) P ∧
        (∫ w, |T f w - T g w| ∂P) ≤ 2 * ∫ a, |f a - g a| ∂mu)
    (hSub : ∀ f g : A → ℝ, Measurable f → Measurable g →
      Integrable f mu → Integrable g mu → T (f - g) =ᵐ[P] T f - T g)
    (B : ℕ → Set A) (hB : ∀ n, MeasurableSet (B n))
    (hmono : Monotone B) (hcover : (⋃ n, B n) = Set.univ)
    (hSq : ∀ (n : ℕ) (f : A → ℝ), Measurable f → Integrable f mu →
      MemLp f 2 mu → (∀ a ∉ B n, f a = 0) →
      Integrable (fun w => (T f w)^2) P ∧
        (∫ w, (T f w)^2 ∂P) = ∫ a, (f a)^2 ∂mu)
    (g : A → ℝ) (hgm : Measurable g) (hgi : Integrable g mu) (hg : MemLp g 2 mu) :
    MemLp (T g) 2 P ∧ (∫ w, (T g w)^2 ∂P) = ∫ a, (g a)^2 ∂mu := by
  sorry
