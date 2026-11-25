-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjHom_mul_pow_cancel
-- name    : GroundTheory.Arith.SchemeCoh.ProjHom.mul_pow_cancel
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:34:53.93263+00:00
-- url     : https://prove2.me/theorems/4d3fa465-9eb4-572c-8be3-aa434b97d061
-- title:
--   Proj Hom: mul pow cancel
-- statement:
--   The Proj Hom construction uses the mul pow cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjHom.lean#L111-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjHom.lean#L111-L116

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
variable (f : A →+* Γ(X, ⊤)) (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)

theorem GroundTheory.Arith.SchemeCoh.ProjHom.mul_pow_cancel {R : Type*} [CommRing R] {v u w c : R} (hc : IsUnit c) (k d : ℕ)
    (h : v * (c ^ d * u) ^ k = c ^ (k • d) * w) : v * u ^ k = w := by sorry
