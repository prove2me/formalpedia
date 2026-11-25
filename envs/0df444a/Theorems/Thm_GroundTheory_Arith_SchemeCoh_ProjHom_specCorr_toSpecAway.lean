-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjHom_specCorr_toSpecAway
-- name    : GroundTheory.Arith.SchemeCoh.ProjHom.specCorr_toSpecAway
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:38:27.430863+00:00
-- url     : https://prove2.me/theorems/7fefc725-820a-43d7-8263-ba50d1645cec
-- title:
--   Proj Hom: spec Corr to Spec Away
-- statement:
--   The Proj Hom construction uses the spec Corr to Spec Away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjHom.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjHom.lean#L39-L43

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

theorem GroundTheory.Arith.SchemeCoh.ProjHom.specCorr_toSpecAway (x : Γ(X, ⊤)) :
    CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Localization.Away x)) ≫ (Scheme.ΓSpecIso _).inv ≫
      (toSpecAway x).appTop = (X.basicOpen x).ι.appTop := by sorry
