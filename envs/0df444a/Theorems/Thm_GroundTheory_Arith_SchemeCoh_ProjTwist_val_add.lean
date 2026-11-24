-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_add
-- name    : GroundTheory.Arith.SchemeCoh.ProjTwist.val_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:36.749023+00:00
-- url     : https://prove2.me/theorems/31a8818d-4399-44ef-bfb8-5b3bfbbfabe6
-- title:
--   Proj Twist: val add
-- statement:
--   The Proj Twist construction uses the val add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwist.lean#L200-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwist.lean#L200-L200

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

theorem GroundTheory.Arith.SchemeCoh.ProjTwist.val_add (s t : Γ(twistingSheaf 𝒜 k, U)) : val (s + t) = val s + val t := by sorry

attribute [defeq] GroundTheory.Arith.SchemeCoh.ProjTwist.val_add
