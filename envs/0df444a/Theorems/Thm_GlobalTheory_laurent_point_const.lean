-- Prove2me | Theorems.Thm_GlobalTheory_laurent_point_const
-- name    : GlobalTheory.laurent_point_const
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:14.372052+00:00
-- url     : https://prove2.me/theorems/c357de1f-2624-47f4-9515-a22a8d2dd002
-- title:
--   Global Theory: laurent point const
-- statement:
--   The Global Theory construction uses the laurent point const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L385-L417
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L385-L417

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

theorem GlobalTheory.laurent_point_const {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsProper B.hom]
    (L : Type) [Field L] (s : Spec (CommRingCat.of L) ⟶ S)
    (f : Spec (CommRingCat.of (AddMonoidAlgebra L ℤ)) ⟶ B.left)
    (hf : f ≫ B.hom = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ s) :
    ∃ k : Spec (CommRingCat.of L) ⟶ B.left,
      f = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ k := by sorry
