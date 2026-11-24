-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_exists_val_eq_of_mem_awayDeg_zero
-- name    : GroundTheory.Arith.SchemeCoh.ProjTwist.exists_val_eq_of_mem_awayDeg_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:28:47.937801+00:00
-- url     : https://prove2.me/theorems/eaa609d5-b6da-415f-80b6-5af9ad0d22b3
-- title:
--   Proj Twist: exists val eq of mem away Deg zero
-- statement:
--   The Proj Twist construction uses the exists val eq of mem away Deg zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwistAway.lean#L93-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwistAway.lean#L93-L103

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

theorem GroundTheory.Arith.SchemeCoh.ProjTwist.exists_val_eq_of_mem_awayDeg_zero {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    {z : Localization.Away f} (hz : z ∈ awayDeg 𝒜 hf hd 0) :
    ∃ z₀ : HomogeneousLocalization.Away 𝒜 f, z₀.val = z := by sorry
