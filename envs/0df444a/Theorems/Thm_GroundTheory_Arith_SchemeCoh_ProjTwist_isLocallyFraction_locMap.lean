-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_isLocallyFraction_locMap
-- name    : GroundTheory.Arith.SchemeCoh.ProjTwist.isLocallyFraction_locMap
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:28:53.028141+00:00
-- url     : https://prove2.me/theorems/975dac08-9738-420c-8444-34f4f0a4fe12
-- title:
--   Proj Twist: is Locally Fraction loc Map
-- statement:
--   The Proj Twist construction uses the is Locally Fraction loc Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwistAway.lean#L145-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwistAway.lean#L145-L150

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

theorem GroundTheory.Arith.SchemeCoh.ProjTwist.isLocallyFraction_locMap {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) {k : ℤ}
    {z : Localization.Away f} (hz : z ∈ awayDeg 𝒜 hf hd k) :
    (isLocallyFraction 𝒜 k).pred
      (fun x : (Proj.basicOpen 𝒜 f : Opens (ProjectiveSpectrum.top 𝒜)) =>
        locMap x.1 (nmem_of_mem x) z) := by sorry
