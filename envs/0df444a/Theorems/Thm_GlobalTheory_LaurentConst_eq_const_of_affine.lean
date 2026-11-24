-- Prove2me | Theorems.Thm_GlobalTheory_LaurentConst_eq_const_of_affine
-- name    : GlobalTheory.LaurentConst.eq_const_of_affine
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:01:34.437862+00:00
-- url     : https://prove2.me/theorems/1ab5e2a0-ec7a-497d-a016-e4a8b160cd9a
-- title:
--   Laurent Const: eq const of affine
-- statement:
--   The Laurent Const construction uses the eq const of affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L271-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExtOfForallQuotient.lean#L271-L286

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

theorem GlobalTheory.LaurentConst.eq_const_of_affine {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) {R : Type}
    [CommRing R] (g : Spec (.of (AddMonoidAlgebra R ℤ)) ⟶ Y) (g₀ g₁ : Spec (.of (PowerSeries R)) ⟶ Y)
    (hg : Set.range g ⊆ U) (hg₀ : Set.range g₀ ⊆ U) (hg₁ : Set.range g₁ ⊆ U)
    (h₀ : Spec.map (CommRingCat.ofHom (atZero R)) ≫ g =
      Spec.map (CommRingCat.ofHom (HahnSeries.ofPowerSeries ℤ R)) ≫ g₀)
    (h₁ : Spec.map (CommRingCat.ofHom (atInf R)) ≫ g =
      Spec.map (CommRingCat.ofHom (HahnSeries.ofPowerSeries ℤ R)) ≫ g₁) :
    g = Spec.map (CommRingCat.ofHom (algebraMap R _)) ≫
      Spec.map (CommRingCat.ofHom PowerSeries.constantCoeff) ≫ g₀ := by sorry
