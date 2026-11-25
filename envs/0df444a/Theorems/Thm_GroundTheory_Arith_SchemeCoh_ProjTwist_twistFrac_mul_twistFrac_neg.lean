-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_twistFrac_mul_twistFrac_neg
-- name    : GroundTheory.Arith.SchemeCoh.ProjTwist.twistFrac_mul_twistFrac_neg
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:13:49.427196+00:00
-- url     : https://prove2.me/theorems/fbfde88a-63e0-4ddf-a87f-f12bc33c42f9
-- title:
--   Proj Twist: twist Frac mul twist Frac neg
-- statement:
--   The Proj Twist construction uses the twist Frac mul twist Frac neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwistLeray.lean#L76-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwistLeray.lean#L76-L82

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

theorem GroundTheory.Arith.SchemeCoh.ProjTwist.twistFrac_mul_twistFrac_neg (u : A) (k : ℤ) (x : ProjectiveSpectrum 𝒜)
    (hx : u ∉ x.asHomogeneousIdeal) : twistFrac u k x hx * twistFrac u (-k) x hx = 1 := by sorry
