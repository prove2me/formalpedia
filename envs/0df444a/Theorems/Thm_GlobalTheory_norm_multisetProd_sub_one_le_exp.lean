-- Prove2me | Theorems.Thm_GlobalTheory_norm_multisetProd_sub_one_le_exp
-- name    : GlobalTheory.norm_multisetProd_sub_one_le_exp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:13:38.959503+00:00
-- url     : https://prove2.me/theorems/4eaea1be-15d9-4b34-b732-03382733a2ad
-- title:
--   Global Theory: norm multiset Prod sub one le exp
-- statement:
--   The Global Theory construction uses the norm multiset Prod sub one le exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NormProdSignMulDetSubmatrixSubOneLe.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NormProdSignMulDetSubmatrixSubOneLe.lean#L11-L19

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

theorem GlobalTheory.norm_multisetProd_sub_one_le_exp (s : Multiset ℂ) {t : ℝ} (ht : 0 ≤ t)
    (hs : ∀ μ ∈ s, ‖μ - 1‖ ≤ t) : ‖s.prod - 1‖ ≤ Real.exp (s.card * t) - 1 := by sorry
