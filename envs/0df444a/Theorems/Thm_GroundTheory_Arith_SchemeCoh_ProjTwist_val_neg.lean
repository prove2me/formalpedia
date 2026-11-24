-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_neg
-- name    : GroundTheory.Arith.SchemeCoh.ProjTwist.val_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:10.739521+00:00
-- url     : https://prove2.me/theorems/913325ec-8cb2-400e-ad07-cea73225bfee
-- title:
--   Proj Twist: val neg
-- statement:
--   The Proj Twist construction uses the val neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwist.lean#L204-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwist.lean#L204-L204

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

theorem GroundTheory.Arith.SchemeCoh.ProjTwist.val_neg (s : Γ(twistingSheaf 𝒜 k, U)) : val (-s) = -val s := by sorry

attribute [defeq] GroundTheory.Arith.SchemeCoh.ProjTwist.val_neg
