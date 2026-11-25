-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_TwoRoots_card_le_nat
-- name    : GlobalTheory.BadShare.TwoRoots.card_le_nat
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:56:43.524875+00:00
-- url     : https://prove2.me/theorems/f58e361d-516f-4b9d-b2bd-61160bba5077
-- title:
--   Two Roots: card le nat
-- statement:
--   The Two Roots construction uses the card le nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardIrreducibleSamePrimeToPartRootsLe.lean#L80-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardIrreducibleSamePrimeToPartRootsLe.lean#L80-L150

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardIrreducibleSamePrimeToPartRootsLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare GlobalTheory.BadShare.TwoRoots

theorem GlobalTheory.BadShare.TwoRoots.card_le_nat (g : ℕ) [Fact g.Prime] (d l : ℕ) (hd : 2 ≤ d) (hl : l.Prime) :
    ((sqSet g d).filter fun P => Irreducible P ∧ ∃ x ∈ P.aroots (AlgebraicClosure (ZMod g)),
      ∃ y ∈ P.aroots (AlgebraicClosure (ZMod g)), x ≠ y ∧ SamePart l x y).card ≤
      l ^ padicValNat l (g ^ d - 1) * g ^ (d / 2) := by sorry
