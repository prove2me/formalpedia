-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_locMap_comp
-- name    : GroundTheory.Arith.SchemeCoh.ProjTwist.locMap_comp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:28:30.33079+00:00
-- url     : https://prove2.me/theorems/f4323eef-06c3-4041-af30-e8234e5a1b9f
-- title:
--   Proj Twist: loc Map comp
-- statement:
--   The Proj Twist construction uses the loc Map comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwistAway.lean#L42-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwistAway.lean#L42-L51

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

theorem GroundTheory.Arith.SchemeCoh.ProjTwist.locMap_comp {f f' : A} (φ : Localization.Away f →+* Localization.Away f')
    (hφ : φ.comp (algebraMap A _) = algebraMap A _) (x : ProjectiveSpectrum 𝒜)
    (hx : f' ∉ x.asHomogeneousIdeal) (hx' : f ∉ x.asHomogeneousIdeal) (z : Localization.Away f) :
    locMap x hx (φ z) = locMap x hx' z := by sorry
