-- Prove2me | Theorems.Thm_GlobalTheory_MatchTerm_tx_eq
-- name    : GlobalTheory.MatchTerm.tx_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:21:35.576917+00:00
-- url     : https://prove2.me/theorems/837773e8-7aad-49e4-a934-a2ab387a5fad
-- title:
--   Match Term: tx eq
-- statement:
--   The Match Term construction uses the tx eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ThetaRecognitionLatticeIsoAndTermsAgree.lean#L52-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ThetaRecognitionLatticeIsoAndTermsAgree.lean#L52-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaMatchingExistsRightTorusTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaConstantTermRepresentativeDependenceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationSeriesTermsNestStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTermStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaRecognitionLatticeIsoAndTermsAgree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex Filter
open scoped BigOperators Topology
open GlobalTheory GlobalTheory.MatchTerm
variable {C : Type} [NormedField C] [IsAlgClosed C] {N N' : NumD C} {n g : ℕ} (μ : Match N N' n)

theorem GlobalTheory.MatchTerm.tx_eq {m : ℕ} (hm : ∃ j, m = n ^ j) {p : N.QT (m ^ 2)} {p' : N'.QT (m ^ 2)} (h : μ.r _ p p') :
    N'.tx m p' = μ.c₀ * N.tx m p := by sorry
