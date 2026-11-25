-- Prove2me | Theorems.Thm_GlobalTheory_AffineComplement_stalkId_vanishingIdeal_compl
-- name    : GlobalTheory.AffineComplement.stalkId_vanishingIdeal_compl
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:17:00.293006+00:00
-- url     : https://prove2.me/theorems/cae087ad-5e40-47fb-b194-66f2f6cd8930
-- title:
--   Affine Complement: stalk Id vanishing Ideal compl
-- statement:
--   The Affine Complement construction uses the stalk Id vanishing Ideal compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsNonzeroLocusEqAffineOpenLocallyFactorial.lean#L62-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsNonzeroLocusEqAffineOpenLocallyFactorial.lean#L62-L90

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

theorem GlobalTheory.AffineComplement.stalkId_vanishingIdeal_compl {X : Scheme.{0}} (U : X.Opens) (x : X)
    (a : X.presheaf.stalk x)
    (h : ∀ q : PrimeSpectrum (X.presheaf.stalk x), X.fromSpecStalk x q ∈ U ↔ a ∉ q.asIdeal) :
    FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal U.compl) x = (Ideal.span {a}).radical := by sorry
