-- Prove2me | Theorems.Thm_GlobalTheory_CardLength_log_card_eq_finsum_length
-- name    : GlobalTheory.CardLength.log_card_eq_finsum_length
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:05:56.252926+00:00
-- url     : https://prove2.me/theorems/5849e948-a997-4187-a786-6323aca4a7e0
-- title:
--   Card Length: log card eq finsum length
-- statement:
--   The Card Length construction uses the log card eq finsum length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LogCardEqFinsumLengthLocalizedMaximal.lean#L118-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LogCardEqFinsumLengthLocalizedMaximal.lean#L118-L143

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogCardEqFinsumLengthLocalizedMaximal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CardLength
variable {R : Type} [CommRing R]

theorem GlobalTheory.CardLength.log_card_eq_finsum_length : ∀ (B : Type) [CommRing B] (N : Type) [AddCommGroup N]
    [Module B N] [Finite N], Real.log (Nat.card N) = ∑ᶠ m : MaximalSpectrum B,
      ((Module.length (Localization.AtPrime m.asIdeal)
        (LocalizedModule m.asIdeal.primeCompl N)).toNat : ℝ) * Real.log (Nat.card (B ⧸ m.asIdeal)) := by sorry
