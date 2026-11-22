-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanRightClippedDiscountedValueMeasurable
-- name    : Kyprianou.Ch01.mckeanRightClippedDiscountedValueMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T18:53:53.116983+00:00
-- url     : https://prove2.me/theorems/1a75d033-726e-4db7-9271-b4c4dd441996
-- title:
--   Finite-horizon clipped discounted McKean candidate is measurable
-- statement:
--   The finite clock T=min(tau,n) is a right-natural stopping time by the already Proved rightNaturalStoppingMinTimeFinite lemma in the exact natural-right filtration. Apply the already Proved mckeanDiscountedValue_rightStoppedMeasurable theorem to the WithTop lift of this finite random time. Since the lift is always finite, the stopped payoff is definitionally the exponential discount times the McKean value evaluated at T. The resulting measurable family is the precise sequence for bounded convergence from finite-horizon optional sampling.
-- source:
--   Kyprianou 2006 Chapter 1 Theorem 1.13, measurable finite-horizon stopped value.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_rightNaturalStoppingMinTimeFinite
import Theorems.Thm_Kyprianou_Ch01_mckeanDiscountedValue_rightStoppedMeasurable
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanRightClippedDiscountedValueMeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (x K q phi : ℝ)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hF : ∀ t, F t = naturalSigmaRight (fun u ω => x + X u ω) t)
    (tau : Ω → WithTop ℝ≥0)
    (hTau : IsNaturalRightStoppingTime (fun t ω => x + X t ω) tau)
    (n : ℕ) :
    let barrier := Real.log (K * phi / (1 + phi))
    let T : Ω → ℝ≥0 := fun ω =>
      (min (tau ω) (((n : ℝ≥0)) : WithTop ℝ≥0)).untopD (n : ℝ≥0)
    Measurable (fun ω : Ω =>
      Real.exp (-q * (T ω : ℝ)) *
        mckeanValue K barrier phi (x + X (T ω) ω)) := by sorry
