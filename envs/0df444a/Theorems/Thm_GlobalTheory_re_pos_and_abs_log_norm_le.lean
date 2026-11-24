-- Prove2me | Theorems.Thm_GlobalTheory_re_pos_and_abs_log_norm_le
-- name    : GlobalTheory.re_pos_and_abs_log_norm_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:22:06.79865+00:00
-- url     : https://prove2.me/theorems/e880c07d-8eeb-4c9b-8a0a-142bcf2c6b6c
-- title:
--   Global Theory: re pos and abs log norm le
-- statement:
--   The Global Theory construction uses the re pos and abs log norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NormProdSignMulDetSubmatrixSubOneLe.lean#L104-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NormProdSignMulDetSubmatrixSubOneLe.lean#L104-L118

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_ScaledBoundInequality
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ImportsAlt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NormProdSignMulDetSubmatrixSubOneLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open Matrix hiding gram
open GlobalTheory

theorem GlobalTheory.re_pos_and_abs_log_norm_le {d : ℂ} {t : ℝ} (ht : t ≤ 1 / 6) (hd : ‖d - 1‖ ≤ 2 * t) :
    0 < d.re ∧ |Real.log ‖d‖| ≤ 3 * t := by sorry
