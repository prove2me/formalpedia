-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_smul
-- name    : GroundTheory.Arith.SchemeCoh.ProjTwist.val_smul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:28:09.599926+00:00
-- url     : https://prove2.me/theorems/48690eca-f47b-4305-8fbb-3a38c1ac76de
-- title:
--   Proj Twist: val smul
-- statement:
--   The Proj Twist construction uses the val smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwist.lean#L208-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwist.lean#L208-L209

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

theorem GroundTheory.Arith.SchemeCoh.ProjTwist.val_smul (t : Γ(Proj 𝒜, U)) (s : Γ(twistingSheaf 𝒜 k, U)) (x : U) :
    val (t • s) x = (t.1 x).val * val s x := by sorry
