-- Prove2me | Theorems.Thm_GlobalTheory_DualTransfer_card_range
-- name    : GlobalTheory.DualTransfer.card_range
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:51:48.444474+00:00
-- url     : https://prove2.me/theorems/e2a6f420-c493-4415-ba2d-83590575fd01
-- title:
--   Dual Transfer: card range
-- statement:
--   The Dual Transfer construction uses the card range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/DivisiblePontryaginAnnihilatorDuality.lean#L35-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/DivisiblePontryaginAnnihilatorDuality.lean#L35-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_DivisiblePontryaginAnnihilatorDuality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DualTransfer

theorem GlobalTheory.DualTransfer.card_range {A B : Type} [AddCommGroup A] [AddCommGroup B] (e : A → B → ℂ)
    (M : AddSubgroup A) (K : AddSubgroup B) (hK : ∀ b, b ∈ K ↔ ∀ a, e a b = 1)
    (f : B →+ AddChar (A ⧸ M) ℂ) (hf : ∀ b (a : A), f b (a : A ⧸ M) = e a b) :
    Nat.card f.range = Nat.card (B ⧸ K) := by sorry
