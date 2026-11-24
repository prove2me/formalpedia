-- Prove2me | Theorems.Thm_GlobalTheory_MatchParts_inG_of_half
-- name    : GlobalTheory.MatchParts.inG_of_half
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:20:50.266793+00:00
-- url     : https://prove2.me/theorems/e662f36f-aa24-4450-a894-4d12c05be737
-- title:
--   Match Parts: in G of half
-- statement:
--   The Match Parts construction uses the in G of half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ThetaRecognitionMatchedPartsDimEq.lean#L133-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ThetaRecognitionMatchedPartsDimEq.lean#L133-L157

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

theorem GlobalTheory.MatchParts.inG_of_half (μ : Match N N' n) {k k' K m : ℕ} (hK : K = k * k') (hm : K = m * m) (hkm : k ∣ m) (hm0 : m ≠ 0)
    (hlev : ∃ j, K = n ^ j) (hdiv : ∀ γ : N.Gt, ∃ γ' : N.Gt, γ' ^ m = γ)
    (H : ∀ p : N.QT K, p.1.1 = 1 → ∃ p', μ.r K p p' ∧ ∃ z, p'.1.1.toAdd = m • z)
    (p : N.QT k) (p' : N'.QT k) (h : μ.r k p p') (hp : N.InG p) : N'.InG p' := by sorry
