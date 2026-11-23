-- Prove2me | Theorems.Thm_GlobalTheory_LabelsAgree_exists_good
-- name    : GlobalTheory.LabelsAgree.exists_good
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:06:14.593351+00:00
-- url     : https://prove2.me/theorems/66ae2691-0a65-43a8-b6fb-89fcc8b56c38
-- title:
--   Labels Agree: exists good
-- statement:
--   The Labels Agree construction uses the exists good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ThetaRecognitionLabelsAgreeOfIso.lean#L206-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ThetaRecognitionLabelsAgreeOfIso.lean#L206-L234

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaConstantTermRepresentativeDependence
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTermStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomTransportStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SymmPairingEqOneOfOddOfDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasisUniqueMinPairSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaRecognitionLabelsAgreeOfIso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good

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
open GlobalTheory GlobalTheory.LabelsAgree

theorem GlobalTheory.LabelsAgree.exists_good {C : Type} [NormedField C] [IsAlgClosed C] {N : NumD C} {n g : ℕ} (hn : (n : C) ≠ 0)
    (hT : N.Tors n g) {j : ℕ} (hj : j ≠ 0) (x : N.X) :
    ∃ p : N.QT ((n ^ j) ^ 2), p.1.1.toAdd = x ∧ ‖N.th (p.1.2.b ^ n ^ j)‖ = 1 := by sorry
