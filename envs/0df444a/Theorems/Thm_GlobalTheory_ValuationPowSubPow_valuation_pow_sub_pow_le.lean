-- Prove2me | Theorems.Thm_GlobalTheory_ValuationPowSubPow_valuation_pow_sub_pow_le
-- name    : GlobalTheory.ValuationPowSubPow.valuation_pow_sub_pow_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:50:14.374312+00:00
-- url     : https://prove2.me/theorems/ed2b8557-5f98-423a-966c-288f84204b8b
-- title:
--   Valuation Pow Sub Pow: valuation pow sub pow le
-- statement:
--   The Valuation Pow Sub Pow construction uses the valuation pow sub pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ValuationPowSubPowLe.lean#L7-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ValuationPowSubPowLe.lean#L7-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ValuationPowSubPowLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.ValuationPowSubPow

theorem GlobalTheory.ValuationPowSubPow.valuation_pow_sub_pow_le {K : Type u_1} {Γ : Type u_2} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ) {a b : K}
    (ha : w a ≤ 1) (hb : w b ≤ 1) (m : ℕ) : w (a ^ m - b ^ m) ≤ w (a - b) := by sorry
