-- Prove2me | Theorems.Thm_GlobalTheory_LaurentConst_exists_extension
-- name    : GlobalTheory.LaurentConst.exists_extension
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:01:44.394623+00:00
-- url     : https://prove2.me/theorems/e4ae4ca8-5446-46f8-bcfe-39cd348eedc1
-- title:
--   Laurent Const: exists extension
-- statement:
--   The Laurent Const construction uses the exists extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L288-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L288-L305

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

theorem GlobalTheory.LaurentConst.exists_extension {Y : Scheme.{0}} (p : Y ⟶ S) [UniversallyClosed p] {L : Type} [Field L]
    (s : Spec (.of L) ⟶ S) (x : Spec (.of (LaurentSeries L)) ⟶ Y)
    (hx : x ≫ p = Spec.map (CommRingCat.ofHom HahnSeries.C) ≫ s) :
    ∃ y : Spec (.of (PowerSeries L)) ⟶ Y,
      Spec.map (CommRingCat.ofHom (HahnSeries.ofPowerSeries ℤ L)) ≫ y = x ∧
      y ≫ p = Spec.map (CommRingCat.ofHom PowerSeries.C) ≫ s := by sorry
