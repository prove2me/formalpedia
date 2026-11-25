-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_mass_hasDiv_le
-- name    : GlobalTheory.BadShare.mass_hasDiv_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:46:57.646529+00:00
-- url     : https://prove2.me/theorems/a890a801-219b-53bb-8694-d7294955360d
-- title:
--   Bad Share: mass has Div le
-- statement:
--   The Bad Share construction uses the mass has Div le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SquarefreeLabelTorusMassHasDivisorOfDegreeLe.lean#L121-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SquarefreeLabelTorusMassHasDivisorOfDegreeLe.lean#L121-L140

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MassDegTypeLeCycleTypeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardPermExistsStableSubsetLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassUnionBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassHasDivisorOfDegreeLe
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
open Polynomial Classical

theorem GlobalTheory.BadShare.mass_hasDiv_le : ∀ (g : ℕ) [Fact g.Prime], ∀ N a : ℕ, 0 < a → a < N →
    _root_.GlobalTheory.BadShare.mass g N (_root_.GlobalTheory.BadShare.HasDiv g a) ≤ 7 / 8 := by sorry
