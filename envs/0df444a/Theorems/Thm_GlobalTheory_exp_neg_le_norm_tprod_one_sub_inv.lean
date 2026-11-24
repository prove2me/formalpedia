-- Prove2me | Theorems.Thm_GlobalTheory_exp_neg_le_norm_tprod_one_sub_inv
-- name    : GlobalTheory.exp_neg_le_norm_tprod_one_sub_inv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:38:14.123635+00:00
-- url     : https://prove2.me/theorems/99f73c4e-493a-4dcc-baf4-f2a3372a4be2
-- title:
--   Global Theory: exp neg le norm tprod one sub inv
-- statement:
--   The Global Theory construction uses the exp neg le norm tprod one sub inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExpNegLeNormTprodOneSubInv.lean#L6-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExpNegLeNormTprodOneSubInv.lean#L6-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExpNegLeNormTprodOneSubInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory IsDedekindDomain NumberField
open GlobalTheory

theorem GlobalTheory.exp_neg_le_norm_tprod_one_sub_inv {ι : Type} (x : ι → ℂ) (B : ℝ)
    (h : ∀ a, ‖x a‖ ≤ 1 / 2) (hs : Summable (fun a => ‖x a‖)) (hB : ∑' a, ‖x a‖ ≤ B) :
    Real.exp (-B) ≤ ‖∏' a, (1 - x a)⁻¹‖ := by sorry
