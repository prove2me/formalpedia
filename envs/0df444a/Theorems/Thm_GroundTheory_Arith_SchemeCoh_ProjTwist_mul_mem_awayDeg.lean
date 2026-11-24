-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_mul_mem_awayDeg
-- name    : GroundTheory.Arith.SchemeCoh.ProjTwist.mul_mem_awayDeg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:32:25.092643+00:00
-- url     : https://prove2.me/theorems/413ea74a-d340-4a90-8ace-9fed589365ef
-- title:
--   Proj Twist: mul mem away Deg
-- statement:
--   The Proj Twist construction uses the mul mem away Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwistAway.lean#L80-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwistAway.lean#L80-L86

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

theorem GroundTheory.Arith.SchemeCoh.ProjTwist.mul_mem_awayDeg {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) {k₁ k₂ : ℤ}
    {z w : Localization.Away f} (hz : z ∈ awayDeg 𝒜 hf hd k₁) (hw : w ∈ awayDeg 𝒜 hf hd k₂) :
    z * w ∈ awayDeg 𝒜 hf hd (k₁ + k₂) := by sorry
