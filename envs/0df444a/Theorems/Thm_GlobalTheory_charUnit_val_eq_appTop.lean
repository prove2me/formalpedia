-- Prove2me | Theorems.Thm_GlobalTheory_charUnit_val_eq_appTop
-- name    : GlobalTheory.charUnit_val_eq_appTop
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:13:02.457859+00:00
-- url     : https://prove2.me/theorems/8db1c97b-8ff5-47f2-a5ac-5b920372d71a
-- title:
--   Global Theory: char Unit val eq app Top
-- statement:
--   The Global Theory construction uses the char Unit val eq app Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsPullbackCompIsoMonHom.lean#L27-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsPullbackCompIsoMonHom.lean#L27-L34

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

theorem GlobalTheory.charUnit_val_eq_appTop (S : Scheme.{0}) (X : Type) [AddCommGroup X] (χ : X) :
    (charUnit S X χ).val = (pullback.fst (splitTorusAff ZU X).hom (toZ S)).appTop.hom
      ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom (AddMonoidAlgebra.single χ 1)) := by sorry
