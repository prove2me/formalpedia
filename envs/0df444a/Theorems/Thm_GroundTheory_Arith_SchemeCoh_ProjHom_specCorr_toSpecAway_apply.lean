-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjHom_specCorr_toSpecAway_apply
-- name    : GroundTheory.Arith.SchemeCoh.ProjHom.specCorr_toSpecAway_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:34:41.402072+00:00
-- url     : https://prove2.me/theorems/4fd644f0-3aa6-509c-8338-288c1fa9aeac
-- title:
--   Proj Hom: spec Corr to Spec Away apply
-- statement:
--   The Proj Hom construction uses the spec Corr to Spec Away apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjHom.lean#L45-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjHom.lean#L45-L49

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

theorem GroundTheory.Arith.SchemeCoh.ProjHom.specCorr_toSpecAway_apply (x : Γ(X, ⊤)) (z : Γ(X, ⊤)) :
    ((Scheme.ΓSpecIso _).inv ≫ (toSpecAway x).appTop) (algebraMap Γ(X, ⊤) (Localization.Away x) z) =
      (X.basicOpen x).ι.appTop z := by sorry
