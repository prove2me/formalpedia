-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_twistMap_bijective
-- name    : GroundTheory.Arith.SchemeCoh.ProjTwist.twistMap_bijective
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:11:54.47515+00:00
-- url     : https://prove2.me/theorems/70342d21-f273-4755-a44b-fad57358d38b
-- title:
--   Proj Twist: twist Map bijective
-- statement:
--   The Proj Twist construction uses the twist Map bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwistLeray.lean#L118-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwistLeray.lean#L118-L138

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwistAway
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjCechModel
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwistLeray
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
universe w w' u
noncomputable section
open GroundTheory.Arith.SchemeCoh.ProjTwist
variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]

theorem GroundTheory.Arith.SchemeCoh.ProjTwist.twistMap_bijective {u : A} (hu : u ∈ 𝒜 1) (k : ℤ) {W : Opens (ProjectiveSpectrum.top 𝒜)}
    (hW : ∀ x : W, u ∉ x.1.asHomogeneousIdeal) : Function.Bijective (twistMap hu k hW) := by sorry
