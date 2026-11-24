-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_exists_section_of_isLocallyFraction_zero
-- name    : GroundTheory.Arith.SchemeCoh.ProjTwist.exists_section_of_isLocallyFraction_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:20:28.136342+00:00
-- url     : https://prove2.me/theorems/ecd92e2e-2d2c-489f-90b6-7f5bed55fc70
-- title:
--   Proj Twist: exists section of is Locally Fraction zero
-- statement:
--   The Proj Twist construction uses the exists section of is Locally Fraction zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwistAway.lean#L155-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwistAway.lean#L155-L178

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
set_option backward.isDefEq.respectTransparency.types false
open ProjectiveSpectrum

theorem GroundTheory.Arith.SchemeCoh.ProjTwist.exists_section_of_isLocallyFraction_zero {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (t : ∀ x : U, Loc 𝒜 x.1) (ht : (isLocallyFraction 𝒜 0).pred t) :
    ∃ t' : (Proj.structureSheaf 𝒜).obj.obj (op U), ∀ x, (t'.1 x).val = t x := by sorry
