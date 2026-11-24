-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_isLocallyFraction_mul
-- name    : GroundTheory.Arith.SchemeCoh.ProjTwist.isLocallyFraction_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:20:23.293208+00:00
-- url     : https://prove2.me/theorems/6e45a6d1-f937-41b8-8733-8813555e6d1e
-- title:
--   Proj Twist: is Locally Fraction mul
-- statement:
--   The Proj Twist construction uses the is Locally Fraction mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwistAway.lean#L131-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwistAway.lean#L131-L143

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwist
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwistAway
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite
universe u
variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]
noncomputable section
open GroundTheory.Arith.SchemeCoh.ProjTwist

theorem GroundTheory.Arith.SchemeCoh.ProjTwist.isLocallyFraction_mul {U : Opens (ProjectiveSpectrum.top 𝒜)} {k₁ k₂ k₃ : ℤ}
    (hk : k₁ + k₂ = k₃) {a b : ∀ x : U, Loc 𝒜 x.1} (ha : (isLocallyFraction 𝒜 k₁).pred a)
    (hb : (isLocallyFraction 𝒜 k₂).pred b) : (isLocallyFraction 𝒜 k₃).pred (a * b) := by sorry
