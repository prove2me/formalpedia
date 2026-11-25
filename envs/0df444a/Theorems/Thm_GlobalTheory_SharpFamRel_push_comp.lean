-- Prove2me | Theorems.Thm_GlobalTheory_SharpFamRel_push_comp
-- name    : GlobalTheory.SharpFamRel.push_comp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:01:40.303439+00:00
-- url     : https://prove2.me/theorems/039cd90e-3863-4aa4-b1be-4abd318b6e58
-- title:
--   Sharp Fam Rel: push comp
-- statement:
--   The Sharp Fam Rel construction uses the push comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/E8SharpFamilyMatrixRelationsDense.lean#L55-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/E8SharpFamilyMatrixRelationsDense.lean#L55-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SharpRelations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_E8SharpFamilyMatrixRelationsDense
import Theorems.Thm_GlobalTheory_SharpRel_push_comp

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

theorem GlobalTheory.SharpFamRel.push_comp {x' : T' ⟶ G'} {x : T ⟶ G} (hx : pushPt h.1.w x' = U ≫ x) {a' : G' ⟶ G'} {a : G ⟶ G}
    (ha : a'.left ≫ φ = φ ≫ a.left) : pushPt h.1.w (x' ≫ a') = U ≫ x ≫ a := by sorry
