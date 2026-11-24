-- Prove2me | Theorems.Thm_GlobalTheory_SW_Emb_det_cor_den
-- name    : GlobalTheory.SW.Emb.det_cor_den
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:44:07.801326+00:00
-- url     : https://prove2.me/theorems/357ac1f1-5e71-4530-810f-bd072f8c43d7
-- title:
--   Emb: det cor den
-- statement:
--   The Emb construction uses the det cor den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/EmbeddingCompatibleWithWeilAndDenominator.lean#L83-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/EmbeddingCompatibleWithWeilAndDenominator.lean#L83-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHSiegelOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EmbeddingCompatibleWithWeilAndDenominator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Emb
noncomputable section
variable {R S : Type} [CommRing R] [CommRing S] {N : ℕ}

theorem GlobalTheory.SW.Emb.det_cor_den (C D : Matrix (Fin N) (Fin N) R) (Z : Matrix (Fin (N + 1)) (Fin (N + 1)) R) :
    (cor 0 C * Z + cor 1 D).det = (C * Z.submatrix Fin.succ Fin.succ + D).det := by sorry
