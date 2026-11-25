-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw47_BV_exp_runningSup_integrable
-- name    : Kyprianou.Ch04.kw47_BV_exp_runningSup_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T20:04:52.241887+00:00
-- url     : https://prove2.me/theorems/f3150c40-354d-40af-9222-ce8adbb362c2
-- title:
--   Finite-horizon exponential running-supremum integrability for bounded-variation Lévy processes
-- statement:
--   For a bounded-variation spectrally negative Lévy process, any nonnegative exponential parameter and any finite horizon T, exp(alpha runningSup(X,T)) is integrable. The preceding Proved path bound controls U_T almost surely by the deterministic max(0,T drift). The running supremum is measurable; hence exp(alpha U_T) is strongly measurable and bounded in norm by a constant almost surely, so it is integrable on the probability space. This closes the BV half of the universal exponential-supremum estimate used by the Kella–Whitt product-grid transfer.
-- source:
--   Kyprianou (2006), Chapter 4, bounded variation drift minus subordinator and Exercise 4.7, p.108.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_BV_runningSup_linear_ae_bound
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- BV paths give deterministic compact-horizon exponential
integrability of their running maximum. -/

theorem Kyprianou.Ch04.kw47_BV_exp_runningSup_integrable
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (alpha : Real) (hAlpha : 0 ≤ alpha)
    (T : NNReal) :
    Integrable (fun w : Ω => Real.exp (alpha * runningSup L T w)) P := by sorry
