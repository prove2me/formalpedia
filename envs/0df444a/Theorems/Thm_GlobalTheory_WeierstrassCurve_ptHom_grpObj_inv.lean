-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_ptHom_grpObj_inv
-- name    : GlobalTheory.WeierstrassCurve.ptHom_grpObj_inv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:48:18.461114+00:00
-- url     : https://prove2.me/theorems/f2b02dcb-a566-5a39-9462-a243fa28a047
-- title:
--   Weierstrass Curve: pt Hom grp Obj inv
-- statement:
--   The Weierstrass Curve construction uses the pt Hom grp Obj inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/ExistsGrpObjIsAddLawHom.lean#L63-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/ExistsGrpObjIsAddLawHom.lean#L63-L66

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

theorem GlobalTheory.WeierstrassCurve.ptHom_grpObj_inv {A : Type} [CommRing A] (ρ : R →+* A) (P : Fin 3 → A)
    (hP : IsUnimodularSol (W.map ρ) P) :
    ptHom W ρ P hP ≫ (GrpObj.inv : schemeOver W ⟶ schemeOver W).left = ptHom W ρ _ hP.neg := by sorry
