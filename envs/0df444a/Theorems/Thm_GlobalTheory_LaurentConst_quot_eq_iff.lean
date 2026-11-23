-- Prove2me | Theorems.Thm_GlobalTheory_LaurentConst_quot_eq_iff
-- name    : GlobalTheory.LaurentConst.quot_eq_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:27:21.083873+00:00
-- url     : https://prove2.me/theorems/561c621d-f4cb-4122-aea8-1a08411d0bfc
-- title:
--   Laurent Const: quot eq iff
-- statement:
--   The Laurent Const construction uses the quot eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L222-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L222-L229

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LaurentConst
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {W Z : Scheme.{0}}

theorem GlobalTheory.LaurentConst.quot_eq_iff (a b : Z ⟶ B.left) (h : b ≫ B.hom = a ≫ B.hom) :
    quot a b h = a ≫ B.hom ≫ (η[B] : 𝟙_ (Over S) ⟶ B).left ↔ a = b := by sorry
