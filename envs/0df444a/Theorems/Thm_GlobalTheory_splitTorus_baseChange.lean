-- Prove2me | Theorems.Thm_GlobalTheory_splitTorus_baseChange
-- name    : GlobalTheory.splitTorus_baseChange
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:01.137067+00:00
-- url     : https://prove2.me/theorems/ccaf094e-6d71-46d9-b9cd-ae4652cba282
-- title:
--   Global Theory: split Torus base Change
-- statement:
--   The Global Theory construction uses the split Torus base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsPullbackCompIsoMonHom.lean#L36-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsPullbackCompIsoMonHom.lean#L36-L45

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.splitTorus_baseChange (S S' : Scheme.{0}) (f : S' ⟶ S) (X : Type) [AddCommGroup X] :
    ∃ e : splitTorus S' X ≅ (Over.pullback f).obj (splitTorus S X), IsMonHom e.hom ∧
      ∀ χ : X, (e.hom.left ≫ pullback.fst (splitTorus S X).hom f).appTop.hom (charUnit S X χ).val =
        (charUnit S' X χ).val := by sorry
