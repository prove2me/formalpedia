-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_mk_mem_awayDeg
-- name    : GroundTheory.Arith.SchemeCoh.ProjTwist.mk_mem_awayDeg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:16:29.044802+00:00
-- url     : https://prove2.me/theorems/6825b45a-c9b4-4fcf-b631-f499964f3c63
-- title:
--   Proj Twist: mk mem away Deg
-- statement:
--   The Proj Twist construction uses the mk mem away Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwistAway.lean#L88-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwistAway.lean#L88-L91

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

theorem GroundTheory.Arith.SchemeCoh.ProjTwist.mk_mem_awayDeg {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) {k : ℤ} {n j : ℕ} {a : A}
    (ha : a ∈ 𝒜 j) (hj : (j : ℤ) = n * d + k) :
    Localization.mk a (fpow f n) ∈ awayDeg 𝒜 hf hd k := by sorry
