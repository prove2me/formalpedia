-- Prove2me | Theorems.Thm_GlobalTheory_AffineComplement_effCartier_of_stalkId_of_isLocallyNoetherian
-- name    : GlobalTheory.AffineComplement.effCartier_of_stalkId_of_isLocallyNoetherian
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:27:48.696259+00:00
-- url     : https://prove2.me/theorems/ea9bbb24-121d-5161-a04c-7910498e21a4
-- title:
--   Affine Complement: eff Cartier of stalk Id of is Locally Noetherian
-- statement:
--   The Affine Complement construction uses the eff Cartier of stalk Id of is Locally Noetherian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsNonzeroLocusEqAffineOpenLocallyFactorial.lean#L18-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsNonzeroLocusEqAffineOpenLocallyFactorial.lean#L18-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__DimEqZero_40b4adf5f58b53e3
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsPowMulMemRangeOfLocalDenominators
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsNonzeroLocusEqAffineOpenLocallyFactorial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory GlobalTheory.AffineComplement
open ReciprocityTheory.AnForm.R

theorem GlobalTheory.AffineComplement.effCartier_of_stalkId_of_isLocallyNoetherian {W : Scheme.{0}} [IsLocallyNoetherian W]
    (G : W.IdealSheafData)
    (hG : ∀ x : W, ∃ t ∈ nonZeroDivisors (W.presheaf.stalk x), FinalTheorems.stalkId G x = Ideal.span {t}) :
    FinalTheorems.EffCartier G := by sorry
