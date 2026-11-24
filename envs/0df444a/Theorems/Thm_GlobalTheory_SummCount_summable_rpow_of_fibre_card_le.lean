-- Prove2me | Theorems.Thm_GlobalTheory_SummCount_summable_rpow_of_fibre_card_le
-- name    : GlobalTheory.SummCount.summable_rpow_of_fibre_card_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:23:33.215815+00:00
-- url     : https://prove2.me/theorems/440b9f0f-eb49-47c5-8f42-9b27bd0a7781
-- title:
--   Summ Count: summable rpow of fibre card le
-- statement:
--   The Summ Count construction uses the summable rpow of fibre card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SummableRpowOfFibreCardLe.lean#L24-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SummableRpowOfFibreCardLe.lean#L24-L65

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

theorem GlobalTheory.SummCount.summable_rpow_of_fibre_card_le (ι : Type) (n : ℕ) (b C t : ℝ) (k : ι → Fin n → ℕ)
    (h : ι → ℝ) (hb : 1 < b) (ht : (n : ℝ) < t)
    (hh : ∀ q, 0 ≤ h q ∧ h q ≤ C * ∏ i, (b ^ k q i)⁻¹)
    (hT : ∀ (m : Fin n → ℕ) (T : Finset ι), (∀ q ∈ T, k q = m) →
      (T.card : ℝ) ≤ C * ∏ i, b ^ (n * m i)) :
    Summable fun q => h q ^ t := by sorry
