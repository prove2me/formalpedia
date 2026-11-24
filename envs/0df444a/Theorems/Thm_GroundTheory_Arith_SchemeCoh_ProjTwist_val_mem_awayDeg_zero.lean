-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_mem_awayDeg_zero
-- name    : GroundTheory.Arith.SchemeCoh.ProjTwist.val_mem_awayDeg_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:28:15.222889+00:00
-- url     : https://prove2.me/theorems/f3ee8cb4-3a03-413f-a319-5977c2483a77
-- title:
--   Proj Twist: val mem away Deg zero
-- statement:
--   The Proj Twist construction uses the val mem away Deg zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwistAway.lean#L125-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwistAway.lean#L125-L129

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

theorem GroundTheory.Arith.SchemeCoh.ProjTwist.val_mem_awayDeg_zero {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (z₀ : HomogeneousLocalization.Away 𝒜 f) : z₀.val ∈ awayDeg 𝒜 hf hd 0 := by sorry
