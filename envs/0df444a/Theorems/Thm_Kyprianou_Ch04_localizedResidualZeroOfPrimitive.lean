-- Prove2me | Theorems.Thm_Kyprianou_Ch04_localizedResidualZeroOfPrimitive
-- name    : Kyprianou.Ch04.localizedResidualZeroOfPrimitive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:29:26.914739+00:00
-- url     : https://prove2.me/theorems/9d9abbc3-1153-54e4-b803-d792c5f547ad
-- title:
--   localizedResidualZeroOfPrimitive
-- statement:
--   Countably many bounded stopped primitive martingales identify a right-continuous density as zero.
-- source:
--   Kyprianou (2006), Exercise 4.3(iii).

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- Countably many bounded stopped primitives identify the original density. -/
theorem Kyprianou.Ch04.localizedResidualZeroOfPrimitive {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (g : ℝ → Ω → ℝ) (tau : ℕ → Ω → WithTop NNReal)
    (C : ℕ → ℝ) (hC : ∀ n, 0 ≤ C n)
    (h : ∀ᵐ w ∂P, Measurable (fun r => g r w) ∧
      (∀ s : ℝ, 0 ≤ s → ContinuousWithinAt (fun r => g r w) (Ici s) s) ∧
      (∀ t : NNReal, ∃ n, (t : WithTop NNReal) < tau n w) ∧
      ∀ n : ℕ, ∀ᵐ r ∂volume.restrict (Ici (0 : ℝ)),
        ‖if (r.toNNReal : WithTop NNReal) < tau n w then g r w else 0‖ ≤ C n)
    (hM : ∀ n, Martingale (fun (t : NNReal) w =>
      ∫ r in Icc (0 : ℝ) (t : ℝ),
        (if (r.toNNReal : WithTop NNReal) < tau n w then g r w else 0) ∂volume) F P) :
    ∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s → g s w = 0 := by
  sorry
