-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_stieltjesPhase_eq_log_sum
-- name    : MetricCodes.Spherical.HigherHierarchy.stieltjesPhase_eq_log_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:34.786068+00:00
-- url     : https://prove2.me/theorems/e31a8fb0-35e1-4a6f-bc85-977c4bad9570
-- title:
--   MetricCodes.Spherical.HigherHierarchy.stieltjesPhase_eq_log_sum
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open MeasureTheory
open scoped BigOperators Interval

theorem MetricCodes.Spherical.HigherHierarchy.stieltjesPhase_eq_log_sum {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) {t : ℝ} (ht : 0 < t) :
    stieltjesPhase a b t =
      Real.log ((t + quadraticCoordinate (a (Fin.last r))) / t) +
        ∑ i : Fin r,
          Real.log ((t + quadraticCoordinate (a i.castSucc)) /
            (t + quadraticCoordinate (b i))) := by sorry
