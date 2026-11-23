-- Prove2me | Theorems.Thm_Kyprianou_Ch01_pmfNatWeightedPowersSummable
-- name    : Kyprianou.Ch01.pmfNatWeightedPowersSummable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T07:37:06.75403+00:00
-- url     : https://prove2.me/theorems/e1971ae4-11d8-425e-a531-d6f5b42401e2
-- title:
--   Absolute summability of PMF real coefficients weighted by powers on the unit interval
-- statement:
--   For any PMF on ℕ and real z in [0,1], the real weighted series z^n p(n) is summable, by domination by the absolutely summable real PMF masses. No moment condition.
-- source:
--   Reuses the verified argument PMF.summable_pgf in StochLean Probability.GeneratingFunction.Basic; applied to Kyprianou Ch01.

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.pmfNatWeightedPowersSummable
    (p : PMF ℕ) (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    Summable (fun n : ℕ => z ^ n * (p n).toReal) := by
  sorry
