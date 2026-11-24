-- Prove2me | Theorems.Thm_GlobalTheory_norm_prod_sum_mul_le_pow
-- name    : GlobalTheory.norm_prod_sum_mul_le_pow
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:13:02.34014+00:00
-- url     : https://prove2.me/theorems/a354e1ee-1eed-4147-9907-d8cde6ad4afc
-- title:
--   Global Theory: norm prod sum mul le pow
-- statement:
--   The Global Theory construction uses the norm prod sum mul le pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/NormProdSumThetaLeExp.lean#L8-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/NormProdSumThetaLeExp.lean#L8-L19

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_NormProdSumThetaLeExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory

theorem GlobalTheory.norm_prod_sum_mul_le_pow {N M : ℕ} (c z : Fin N → Fin M → ℂ) {C B : ℝ}
    (hC : 0 ≤ C) (hc : ∀ k t, ‖c k t‖ ≤ C) (hz : ∀ k t, ‖z k t‖ ≤ B) :
    ‖∏ k, ∑ t, c k t * z k t‖ ≤ (M * (C * B)) ^ N := by sorry
