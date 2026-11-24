-- Prove2me | Theorems.Thm_GlobalTheory_MatchParts_card_le_of_rel
-- name    : GlobalTheory.MatchParts.card_le_of_rel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:24:03.517778+00:00
-- url     : https://prove2.me/theorems/a96cae71-64e6-4ac4-9aa6-af5adb349154
-- title:
--   Match Parts: card le of rel
-- statement:
--   The Match Parts construction uses the card le of rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ThetaRecognitionMatchedPartsDimEq.lean#L170-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ThetaRecognitionMatchedPartsDimEq.lean#L170-L173

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TxCosetCriterionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaRecognitionMatchedPartsDimEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.MatchParts
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ}

theorem GlobalTheory.MatchParts.card_le_of_rel {α β : Type} [Finite β] (R : α → β → Prop) (h : ∀ a, ∃ b, R a b)
    (hi : ∀ a a' b, R a b → R a' b → a = a') : Nat.card α ≤ Nat.card β := by sorry
