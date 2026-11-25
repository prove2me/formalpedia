-- Prove2me | Theorems.Thm_GlobalTheory_ProjSpace_baseChangeIso_coord
-- name    : GlobalTheory.ProjSpace.baseChangeIso_coord
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:21:53.398638+00:00
-- url     : https://prove2.me/theorems/d75193fd-e59b-5dc0-9d6d-70f2fd47991e
-- title:
--   Proj Space: base Change Iso coord
-- statement:
--   The Proj Space construction uses the base Change Iso coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TwistingSheafOneChartEqPreimageStandardChart.lean#L576-L583
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TwistingSheafOneChartEqPreimageStandardChart.lean#L576-L583

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AwayToSectionFromZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi (LB res pullU)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG lbPow LBIso)
open GlobalTheory.ProjFrac GlobalTheory.QCoh.Qcqs
attribute [local instance] MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.ProjSpace
variable (R : Type) [CommRing R] (N : ℕ)
variable {R N}
variable (R N)
variable {R N}
variable (R N)
variable {R} {R' : Type} [CommRing R'] (φ : R →+* R')

theorem GlobalTheory.ProjSpace.baseChangeIso_coord (k i : Fin (N + 1)) (j : PUnit → Fin (N + 1)) :
    resG _ (inf_le_left : (O1 R' N).U i ⊓ ((O1 R N).pull (baseChange N φ)).U j ≤ _) ((coord R' N k).f i) =
      ((baseChangeIso N φ).s (i, j)).val *
        resG _ (inf_le_right.trans (LB.wchart_le (O1 R N) (fun _ => baseChange N φ) j PUnit.unit))
          (((baseChange N φ).app ((O1 R N).U (j PUnit.unit))).hom ((coord R N k).f (j PUnit.unit))) := by sorry
