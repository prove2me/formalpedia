-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_toSection_bijective
-- name    : GroundTheory.Arith.SchemeCoh.ProjTwist.toSection_bijective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:28:13.521799+00:00
-- url     : https://prove2.me/theorems/6689f3f1-1eee-4468-bc38-7725579d8f2b
-- title:
--   Proj Twist: to Section bijective
-- statement:
--   The Proj Twist construction uses the to Section bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwistAway.lean#L180-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwistAway.lean#L180-L255

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

theorem GroundTheory.Arith.SchemeCoh.ProjTwist.toSection_bijective {f u g : A} {e : ℕ} (hu : u ∈ 𝒜 1) (hg : g ∈ 𝒜 e)
    (hfug : f = u * g) (hf : f ∈ 𝒜 (e + 1)) (k : ℤ) :
    Function.Bijective (toSection hf (Nat.succ_pos e) k) := by sorry
