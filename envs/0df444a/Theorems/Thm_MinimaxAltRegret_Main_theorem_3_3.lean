-- Prove2me | Theorems.Thm_MinimaxAltRegret_Main_theorem_3_3
-- name    : MinimaxAltRegret.Main.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:55:40.774643+00:00
-- url     : https://prove2.me/theorems/6b95d2c9-dd8e-4289-968c-422269d67937
-- title:
--   Theorem 3.3 — Algorithm 1 has regret at most 10 log d
-- statement:
--   For every positive number d of experts, every positive integer horizon T, and every adaptive loss sequence ell_1,...,ell_T in [-1,1]^d, Corrected AltHedge (Algorithm 1) at eta=1/10 satisfies
--
--   $$R_T^{\mathrm{exp}}\le10\log d.$$
--
--   The algorithm includes its terminal corrected action p_(T+1). The assertion is pathwise for every loss sequence, so it applies to all permitted adaptive environments. It retains d=1 and horizons below log_2 d, as in the upper theorem; the lower-bound horizon restriction is absent. This supplies the matching experts upper bound.
--
--   Differences from the source:
--   - encoding: rounds 1 through T and the terminal action x_(T+1) → zero-based losses and actions, with action T terminal and source score R_t stored at index t; reason: a bijective reindexing preserves every summand and includes the same terminal update
--   - encoding: the maximum of expert comparator regret over the simplex → the real sSup of the same comparator-regret image; reason: for d>=1 the finite simplex is nonempty and compact and the comparator objective is continuous, so the maximum is attained and equals this sSup
-- source:
--   Mengxiao Zhang, STOC 2027 submission #57 (October 2026), printed p. 9 / PDF p. 10, Theorem 3.3; SHA-256 6db5a23e9e92d250b4dea7995bf34c9930d39a95df90f5d3fdc715ca26044f31

import Mathlib
import Definitions.Def_MinimaxAltRegret_Main_Experts

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace MinimaxAltRegret.Main

theorem theorem_3_3 :
  ∀ (d T : ℕ), 0 < d → 0 < T → ∀ ℓ : ℕ → ExpertVector d,
  expertLosses d T ℓ → expertRegret T ℓ (expertAlgorithm T ℓ) ≤ 10*Real.log (d : ℝ) := by sorry

end MinimaxAltRegret.Main
