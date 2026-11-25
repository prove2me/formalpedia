-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjHom_specCorr_comp
-- name    : GroundTheory.Arith.SchemeCoh.ProjHom.specCorr_comp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:33:13.664797+00:00
-- url     : https://prove2.me/theorems/9639bcca-d58f-4f43-ac91-4557019b413e
-- title:
--   Proj Hom: spec Corr comp
-- statement:
--   The Proj Hom construction uses the spec Corr comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjHom.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjHom.lean#L17-L23

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_TwistingSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ProjHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open AlgebraicGeometry CategoryTheory Limits Opposite HomogeneousLocalization
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
universe u
noncomputable section
variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
open GroundTheory.Arith.SchemeCoh.ProjHom
variable {X : Scheme.{u}}

theorem GroundTheory.Arith.SchemeCoh.ProjHom.specCorr_comp {Y : Scheme.{u}} {R S : CommRingCat.{u}} (a : Y ⟶ Spec S) (φ : R ⟶ S) :
    (Scheme.ΓSpecIso R).inv ≫ (a ≫ Spec.map φ).appTop =
      φ ≫ (Scheme.ΓSpecIso S).inv ≫ a.appTop := by sorry
