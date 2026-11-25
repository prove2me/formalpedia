-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_twistMap_apply
-- name    : GroundTheory.Arith.SchemeCoh.ProjTwist.twistMap_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:19:45.702431+00:00
-- url     : https://prove2.me/theorems/b64799b0-fe3e-452b-aced-2f2af4b36ded
-- title:
--   Proj Twist: twist Map apply
-- statement:
--   The Proj Twist construction uses the twist Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwistLeray.lean#L113-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwistLeray.lean#L113-L116

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

theorem GroundTheory.Arith.SchemeCoh.ProjTwist.twistMap_apply {u : A} (hu : u ∈ 𝒜 1) (k : ℤ) {W : Opens (ProjectiveSpectrum.top 𝒜)}
    (hW : ∀ x : W, u ∉ x.1.asHomogeneousIdeal)
    (t : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op W)) (x : W) :
    (twistMap hu k hW t).1 x = twistFrac u k x.1 (hW x) * (t.1 x).val := by sorry
