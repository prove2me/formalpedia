-- Prove2me | Theorems.Thm_GlobalTheory_norm_det_one_add_sub_one_le_exp
-- name    : GlobalTheory.norm_det_one_add_sub_one_le_exp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:19:54.547798+00:00
-- url     : https://prove2.me/theorems/f120c2e6-9db0-4ae0-95cd-d33768ed5100
-- title:
--   Global Theory: norm det one add sub one le exp
-- statement:
--   The Global Theory construction uses the norm det one add sub one le exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NormProdSignMulDetSubmatrixSubOneLe.lean#L21-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NormProdSignMulDetSubmatrixSubOneLe.lean#L21-L45

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

theorem GlobalTheory.norm_det_one_add_sub_one_le_exp {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) {ε : ℝ} (hε : 0 ≤ ε) (hM : ∀ a b, ‖M a b‖ ≤ ε) :
    ‖(1 + M).det - 1‖ ≤ Real.exp (Fintype.card n * (Fintype.card n * ε)) - 1 := by sorry
