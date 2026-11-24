-- Prove2me | Theorems.Thm_GlobalTheory_norm_gram_sign_sub_le
-- name    : GlobalTheory.norm_gram_sign_sub_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:14:16.124116+00:00
-- url     : https://prove2.me/theorems/7f362d77-b4f1-47ec-ae49-d0e2e3da99b3
-- title:
--   Global Theory: norm gram sign sub le
-- statement:
--   The Global Theory construction uses the norm gram sign sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NormProdSignMulDetSubmatrixSubOneLe.lean#L47-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NormProdSignMulDetSubmatrixSubOneLe.lean#L47-L73

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

theorem GlobalTheory.norm_gram_sign_sub_le {r : ℕ} (j : Fin r → ℂ) (hj : ∀ a, ‖j a‖ = 1)
    (z : Matrix (Fin r) (Fin r) ℂ) {δ : ℝ} (hδ : 0 ≤ δ) (hr : r * δ ≤ 1) (hz : ∀ a b, ‖z a b‖ ≤ δ)
    (a b : Fin r) :
    ‖((1 + z)ᵀ * diagonal j * (1 + z).map star - diagonal j : Matrix (Fin r) (Fin r) ℂ) a b‖ ≤ 3 * δ := by sorry
