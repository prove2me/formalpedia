-- Prove2me | Theorems.Thm_GlobalTheory_LaurentConst_specMap_comp
-- name    : GlobalTheory.LaurentConst.specMap_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:04.836803+00:00
-- url     : https://prove2.me/theorems/df1e3841-0123-4251-a45e-b07a303a8e1b
-- title:
--   Laurent Const: spec Map comp
-- statement:
--   The Laurent Const construction uses the spec Map comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L307-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L307-L311

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

theorem GlobalTheory.LaurentConst.specMap_comp {A C D : Type} [CommRing A] [CommRing C] [CommRing D] (α : C →+* A)
    (β : D →+* C) {Y : Scheme.{0}} (f : Spec (.of D) ⟶ Y) :
    Spec.map (CommRingCat.ofHom α) ≫ Spec.map (CommRingCat.ofHom β) ≫ f =
      Spec.map (CommRingCat.ofHom (α.comp β)) ≫ f := by sorry
