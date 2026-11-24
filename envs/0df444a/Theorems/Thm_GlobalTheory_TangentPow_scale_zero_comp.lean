-- Prove2me | Theorems.Thm_GlobalTheory_TangentPow_scale_zero_comp
-- name    : GlobalTheory.TangentPow.scale_zero_comp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:58.950804+00:00
-- url     : https://prove2.me/theorems/d32070b7-df91-49ec-8548-046f77650eeb
-- title:
--   Tangent Pow: scale zero comp
-- statement:
--   The Tangent Pow construction uses the scale zero comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/PowEqScaleAndExistsUniqueTorsion.lean#L70-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/PowEqScaleAndExistsUniqueTorsion.lean#L70-L72

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowEqScaleAndExistsUniqueTorsion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.TangentPow
variable {O : Type} [CommRing O] {R : Type} [CommRing R] [Algebra O R]
variable {G : Over (Spec (CommRingCat.of O))} [GrpObj G] {y : specO O (DualNumber R) ⟶ G}

theorem GlobalTheory.TangentPow.scale_zero_comp (hy : ptMap (TrivSqZeroExt.fstHom O R R) ≫ y = 1) :
    scale O (0 : R) ≫ y = 1 := by sorry
