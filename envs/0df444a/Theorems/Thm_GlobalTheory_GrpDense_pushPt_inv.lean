-- Prove2me | Theorems.Thm_GlobalTheory_GrpDense_pushPt_inv
-- name    : GlobalTheory.GrpDense.pushPt_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:46:28.723553+00:00
-- url     : https://prove2.me/theorems/4aca339b-eb16-47c3-a862-6ae74cd2d143
-- title:
--   Grp Dense: push Pt inv
-- statement:
--   The Grp Dense construction uses the push Pt inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GrpObjOfDenseOpen.lean#L88-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GrpObjOfDenseOpen.lean#L88-L92

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.GrpDense
variable {Z U : Scheme.{0}} {j : U ⟶ Z}
variable {G : Over Z} {A : Over U} {φ : A.left ⟶ G.left}
variable [GrpObj A] (w : φ ≫ G.hom = A.hom ≫ j)

theorem GlobalTheory.GrpDense.pushPt_inv {i : G ⟶ G} (hi : φ ≫ i.left = (ι[A]).left ≫ φ) {T : Over U} (x : T ⟶ A) :
    pushPt w x ≫ i = pushPt w x⁻¹ := by sorry
