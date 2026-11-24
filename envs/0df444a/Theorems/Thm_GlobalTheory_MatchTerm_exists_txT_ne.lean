-- Prove2me | Theorems.Thm_GlobalTheory_MatchTerm_exists_txT_ne
-- name    : GlobalTheory.MatchTerm.exists_txT_ne
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:24:21.174488+00:00
-- url     : https://prove2.me/theorems/99ebc34e-bae7-429e-be42-234ed04bc55f
-- title:
--   Match Term: exists tx T ne
-- statement:
--   The Match Term construction uses the exists tx T ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ThetaRecognitionLatticeIsoAndTermsAgree.lean#L24-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ThetaRecognitionLatticeIsoAndTermsAgree.lean#L24-L37

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

theorem GlobalTheory.MatchTerm.exists_txT_ne {C : Type} [NormedField C] [IsAlgClosed C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}
    (hq : N.Int q) {n g : ℕ} (hn : Odd n) (hC : (n : C) ≠ 0) (hT : N.Tors n g) (x : N.X) :
    ∃ p : N.QT ((n ^ 1) ^ 2), p.1.1 = 1 ∧ N.txT (n ^ 1) p x ≠ 0 := by sorry
