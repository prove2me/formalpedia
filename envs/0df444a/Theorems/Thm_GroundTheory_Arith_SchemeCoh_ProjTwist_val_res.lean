-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_res
-- name    : GroundTheory.Arith.SchemeCoh.ProjTwist.val_res
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:28:04.529476+00:00
-- url     : https://prove2.me/theorems/05cbe81d-7bfc-46b6-b538-7c5e612cb2c2
-- title:
--   Proj Twist: val res
-- statement:
--   The Proj Twist construction uses the val res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwist.lean#L211-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwist.lean#L211-L212

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwist
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
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
open GroundTheory.Arith.SchemeCoh.ProjTwist
variable {𝒜} {k : ℤ} {U V : (Proj 𝒜).Opens}

theorem GroundTheory.Arith.SchemeCoh.ProjTwist.val_res (h : V ≤ U) (s : Γ(twistingSheaf 𝒜 k, U)) (x : V) :
    val ((twistingSheaf 𝒜 k).presheaf.map (homOfLE h).op s) x = val s ⟨x.1, h x.2⟩ := by sorry
