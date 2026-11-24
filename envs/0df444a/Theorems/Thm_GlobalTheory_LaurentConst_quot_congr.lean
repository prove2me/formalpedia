-- Prove2me | Theorems.Thm_GlobalTheory_LaurentConst_quot_congr
-- name    : GlobalTheory.LaurentConst.quot_congr
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:01:18.121803+00:00
-- url     : https://prove2.me/theorems/bbc5b687-19b9-4a71-8f27-a983dd2f628b
-- title:
--   Laurent Const: quot congr
-- statement:
--   The Laurent Const construction uses the quot congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L231-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L231-L233

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

theorem GlobalTheory.LaurentConst.quot_congr {a b a' b' : Z ⟶ B.left} (h : b ≫ B.hom = a ≫ B.hom)
    (h' : b' ≫ B.hom = a' ≫ B.hom) (ha : a = a') (hb : b = b') : quot a b h = quot a' b' h' := by sorry
