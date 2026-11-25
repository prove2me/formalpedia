-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_TwoRoots_card_irreducible_samePart_le
-- name    : GlobalTheory.BadShare.TwoRoots.card_irreducible_samePart_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:56:53.828631+00:00
-- url     : https://prove2.me/theorems/77ff737c-c4e0-4d89-aa76-e22d7b6e31b7
-- title:
--   Two Roots: card irreducible same Part le
-- statement:
--   The Two Roots construction uses the card irreducible same Part le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardIrreducibleSamePrimeToPartRootsLe.lean#L152-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardIrreducibleSamePrimeToPartRootsLe.lean#L152-L172

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

theorem GlobalTheory.BadShare.TwoRoots.card_irreducible_samePart_le : ∀ (g : ℕ) [Fact g.Prime], ∀ (N d l : ℕ), 2 ≤ d → d ≤ N → l.Prime → ¬ BB g N l → (((sqSet g d).filter fun P => Irreducible P ∧ ∃ x ∈ P.aroots (AlgebraicClosure (ZMod g)), ∃ y ∈ P.aroots (AlgebraicClosure (ZMod g)), x ≠ y ∧ SamePart l x y).card : ℝ) ≤ (g : ℝ) ^ ((3 * d : ℝ) / 4) := by sorry
