-- Prove2me | Theorems.Thm_GlobalTheory_SharpFamRel_eq_down
-- name    : GlobalTheory.SharpFamRel.eq_down
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:44:08.714457+00:00
-- url     : https://prove2.me/theorems/99d7e518-f43f-4ad1-b25d-4280bd8991a8
-- title:
--   Sharp Fam Rel: eq down
-- statement:
--   The Sharp Fam Rel construction uses the eq down property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/E8SharpFamilyMatrixRelationsDense.lean#L42-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/E8SharpFamilyMatrixRelationsDense.lean#L42-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SharpRelations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_E8SharpFamilyMatrixRelationsDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.SharpFamRel
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
  (h : IsGrpPullback G' G f φ)
variable {T : Over S} {T' : Over S'} (U : Over.mk (T'.hom ≫ f) ⟶ T)

theorem GlobalTheory.SharpFamRel.eq_down (hU : Epi U.left) {x' y' : T' ⟶ G'} {x y : T ⟶ G} (hx : pushPt h.1.w x' = U ≫ x)
    (hy : pushPt h.1.w y' = U ≫ y) (e : x' = y') : x = y := by sorry
