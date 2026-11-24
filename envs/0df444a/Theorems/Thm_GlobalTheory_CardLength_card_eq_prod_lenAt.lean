-- Prove2me | Theorems.Thm_GlobalTheory_CardLength_card_eq_prod_lenAt
-- name    : GlobalTheory.CardLength.card_eq_prod_lenAt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:06:02.267827+00:00
-- url     : https://prove2.me/theorems/43fbc789-a3e5-4b5f-9fd6-d79068411dbc
-- title:
--   Card Length: card eq prod len At
-- statement:
--   The Card Length construction uses the card eq prod len At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LogCardEqFinsumLengthLocalizedMaximal.lean#L71-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LogCardEqFinsumLengthLocalizedMaximal.lean#L71-L116

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

theorem GlobalTheory.CardLength.card_eq_prod_lenAt : ∀ (n : ℕ) (Q : Type) [AddCommGroup Q] [Module R Q] [Finite Q],
    Nat.card Q = n → ∃ k : MaximalSpectrum R →₀ ℕ,
      (∀ w : MaximalSpectrum R, lenAt w.asIdeal Q = (k w : ℕ∞)) ∧
      Nat.card Q = k.prod fun w j => Nat.card (R ⧸ w.asIdeal) ^ j := by sorry
