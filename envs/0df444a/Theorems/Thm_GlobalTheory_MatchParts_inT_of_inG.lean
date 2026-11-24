-- Prove2me | Theorems.Thm_GlobalTheory_MatchParts_inT_of_inG
-- name    : GlobalTheory.MatchParts.inT_of_inG
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:23:05.498891+00:00
-- url     : https://prove2.me/theorems/2cf28cdf-04e1-4022-a792-95337d8bc579
-- title:
--   Match Parts: in T of in G
-- statement:
--   The Match Parts construction uses the in T of in G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ThetaRecognitionMatchedPartsDimEq.lean#L159-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ThetaRecognitionMatchedPartsDimEq.lean#L159-L168

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

theorem GlobalTheory.MatchParts.inT_of_inG (μ : Match N N' n) (j : ℕ)
    (hG : ∀ p p', μ.r (n ^ j) p p' → N'.InG p' → N.InG p)
    (hT : ∀ p : N.QT (n ^ j), N.InT p → ∀ p' : N.QT (n ^ j), p'.1.1 = 1 → N.wp p p' = 1)
    (hT' : ∀ p : N'.QT (n ^ j), (∀ p' : N'.QT (n ^ j), p'.1.1 = 1 → N'.wp p p' = 1) → N'.InT p)
    (p : N.QT (n ^ j)) (p' : N'.QT (n ^ j)) (h : μ.r _ p p') (hp : N.InT p) : N'.InT p' := by sorry
