-- Prove2me | Theorems.Thm_GlobalTheory_SummCount_pow_mul_inv_rpow_eq
-- name    : GlobalTheory.SummCount.pow_mul_inv_rpow_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:23:36.653847+00:00
-- url     : https://prove2.me/theorems/38c57db6-b359-472c-8736-b8e1b2bfe47b
-- title:
--   Summ Count: pow mul inv rpow eq
-- statement:
--   The Summ Count construction uses the pow mul inv rpow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SummableRpowOfFibreCardLe.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SummableRpowOfFibreCardLe.lean#L15-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SummableRpowOfFibreCardLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SummCount

theorem GlobalTheory.SummCount.pow_mul_inv_rpow_eq {b t : ℝ} (hb : 0 < b) (n m : ℕ) :
    b ^ (n * m) * ((b ^ m)⁻¹) ^ t = (b ^ ((n : ℝ) - t)) ^ m := by sorry
