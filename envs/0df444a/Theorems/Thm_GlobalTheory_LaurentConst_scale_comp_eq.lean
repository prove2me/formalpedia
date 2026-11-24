-- Prove2me | Theorems.Thm_GlobalTheory_LaurentConst_scale_comp_eq
-- name    : GlobalTheory.LaurentConst.scale_comp_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:01:35.736979+00:00
-- url     : https://prove2.me/theorems/79bffac7-d9a1-4b78-b668-966a81f89291
-- title:
--   Laurent Const: scale comp eq
-- statement:
--   The Laurent Const construction uses the scale comp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L313-L381
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L313-L381

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

theorem GlobalTheory.LaurentConst.scale_comp_eq [UniversallyClosed B.hom] {L R : Type} [Field L] [CommRing R]
    (s : Spec (.of L) ⟶ S) (f : Spec (.of (AddMonoidAlgebra L ℤ)) ⟶ B.left)
    (hf : f ≫ B.hom = Spec.map (CommRingCat.ofHom (algebraMap L _)) ≫ s)
    (r : L →+* R) (t : Rˣ) (ht : IsNilpotent ((t : R) - 1)) :
    Spec.map (CommRingCat.ofHom (scale r t)) ≫ f = Spec.map (CommRingCat.ofHom (scale r 1)) ≫ f := by sorry
