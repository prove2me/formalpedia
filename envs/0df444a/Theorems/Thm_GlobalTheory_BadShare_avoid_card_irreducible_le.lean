-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_avoid_card_irreducible_le
-- name    : GlobalTheory.BadShare.avoid_card_irreducible_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:48:07.478781+00:00
-- url     : https://prove2.me/theorems/0d3cc08d-6d0a-4e8c-b71c-3337b9df638b
-- title:
--   Bad Share: avoid card irreducible le
-- statement:
--   The Bad Share construction uses the avoid card irreducible le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MassNotRootsAvoidLe.lean#L25-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MassNotRootsAvoidLe.lean#L25-L88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassDivisorBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumPrimePowerPartPowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumLeProdOfTwoLeNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PowPadicValEqOneOfPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassUnionBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MassNotRootsAvoidLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare

theorem GlobalTheory.BadShare.avoid_card_irreducible_le {g : ℕ} [Fact g.Prime] (c : (ZMod g)ˣ) (d : ℕ) (hd : 1 ≤ d) (h2 : 2 ∣ g - 1) :
    d * ((sqSet g d).filter fun P => Irreducible P ∧ ¬ RootsAvoid g c P).card ≤
      ∑ l ∈ (g ^ d - 1).primeFactors, l ^ padicValNat l (g ^ d - 1) := by sorry
