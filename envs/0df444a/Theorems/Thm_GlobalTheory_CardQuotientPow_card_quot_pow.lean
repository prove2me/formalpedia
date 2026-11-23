-- Prove2me | Theorems.Thm_GlobalTheory_CardQuotientPow_card_quot_pow
-- name    : GlobalTheory.CardQuotientPow.card_quot_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:45.154265+00:00
-- url     : https://prove2.me/theorems/a85930e0-c177-443a-969d-57fdee9b511f
-- title:
--   Card Quotient Pow: card quot pow
-- statement:
--   The Card Quotient Pow construction uses the card quot pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardQuotPow.lean#L7-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardQuotPow.lean#L7-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardQuotPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CardQuotientPow
open Module Submodule

theorem GlobalTheory.CardQuotientPow.card_quot_pow {R : Type} [CommRing R] [IsDomain R] {p : R} (hp : Irreducible p) (k : ℕ) :
    Nat.card (R ⧸ Ideal.span {p ^ k}) = Nat.card (R ⧸ Ideal.span {p}) ^ k := by sorry
