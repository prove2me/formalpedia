-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_isAddLawHom_mul
-- name    : GlobalTheory.WeierstrassCurve.isAddLawHom_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:49:03.49351+00:00
-- url     : https://prove2.me/theorems/ffc35e68-3857-5920-8f3a-ce4ce9041782
-- title:
--   Weierstrass Curve: is Add Law Hom mul
-- statement:
--   The Weierstrass Curve construction uses the is Add Law Hom mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/ExistsGrpObjIsAddLawHom.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/ExistsGrpObjIsAddLawHom.lean#L33-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsLiftAddOfIsReducedEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HomExtOfLocalRingPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsEqPtHomOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_ExistsGrpObjIsAddLawHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw
open GlobalTheory GlobalTheory.WeierstrassCurve
variable {R : Type} [CommRing R] (W : _root_.WeierstrassCurve R)
variable [W.IsElliptic]

theorem GlobalTheory.WeierstrassCurve.isAddLawHom_mul : IsAddLawHom W μ[schemeOver W] := by sorry
