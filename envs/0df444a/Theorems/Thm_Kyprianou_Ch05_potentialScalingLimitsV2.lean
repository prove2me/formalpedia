-- Prove2me | Theorems.Thm_Kyprianou_Ch05_potentialScalingLimitsV2
-- name    : Kyprianou.Ch05.potentialScalingLimitsV2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T20:36:32.285094+00:00
-- url     : https://prove2.me/theorems/eda6c236-b311-4b8f-862b-aa223660feeb
-- title:
--   potentialScalingLimits (corrected reciprocal factor)
-- statement:
--   Use the slowly varying factor L of the reciprocal exponent, so Phi(1/x) = x^(-rho)/L(x). The potential transform and cumulative asymptotic then use L multiplicatively.
-- source:
--   Kyprianou (2006), Lemma 5.17, corrected reciprocal factor.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Corrected reciprocal slowly varying factor for the potential measure. -/
theorem potentialScalingLimitsV2
    (U : Measure Real) (Phi L : Real → Real) (rho : Real)
    (hRho : 0 ≤ rho)
    (hPhi : ∀ x : Real, 0 < x → Phi (1 / x) = x ^ (-rho) / L x) :
  ((SlowlyVaryingAtInfinity L →
     Tendsto
       (fun x : Real =>
         ((U) (Set.Icc (0 : Real) x)).toReal /
           (x ^ rho * L x / Real.Gamma (1 + rho)))
       atTop (nhds 1) →
     ∀ lambda : Real, 0 < lambda →
       Tendsto
         (fun x : Real =>
           ((U) (Set.Icc (0 : Real) (lambda * x))).toReal * Phi (1 / x))
         atTop (nhds (lambda ^ rho / Real.Gamma (1 + rho)))) ∧
   (SlowlyVaryingAtZero L →
     Tendsto
       (fun x : Real =>
         ((U) (Set.Icc (0 : Real) x)).toReal /
           (x ^ rho * L x / Real.Gamma (1 + rho)))
       (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1) →
     ∀ lambda : Real, 0 < lambda →
       Tendsto
         (fun x : Real =>
           ((U) (Set.Icc (0 : Real) (lambda * x))).toReal * Phi (1 / x))
         (nhdsWithin (0 : Real) (Set.Ioi 0))
         (nhds (lambda ^ rho / Real.Gamma (1 + rho))))) := by
  sorry

end Kyprianou.Ch05
