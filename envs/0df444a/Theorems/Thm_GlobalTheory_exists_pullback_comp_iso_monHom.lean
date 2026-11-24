-- Prove2me | Theorems.Thm_GlobalTheory_exists_pullback_comp_iso_monHom
-- name    : GlobalTheory.exists_pullback_comp_iso_monHom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:34.960697+00:00
-- url     : https://prove2.me/theorems/22475697-4da9-444e-af5c-03ab9f6b9a9f
-- title:
--   Global Theory: exists pullback comp iso mon Hom
-- statement:
--   The Global Theory construction uses the exists pullback comp iso mon Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsPullbackCompIsoMonHom.lean#L11-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsPullbackCompIsoMonHom.lean#L11-L25

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

theorem GlobalTheory.exists_pullback_comp_iso_monHom {T S' S : Scheme.{0}} (f : S' ⟶ S) (g : S ⟶ T) (h : S' ⟶ T)
    (hh : h = f ≫ g) (G : Over T) [GrpObj G] :
    ∃ e : (Over.pullback h).obj G ≅ (Over.pullback f).obj ((Over.pullback g).obj G),
      IsMonHom e.hom ∧
        e.hom.left ≫ pullback.fst ((Over.pullback g).obj G).hom f ≫ pullback.fst G.hom g =
          pullback.fst G.hom h := by sorry
