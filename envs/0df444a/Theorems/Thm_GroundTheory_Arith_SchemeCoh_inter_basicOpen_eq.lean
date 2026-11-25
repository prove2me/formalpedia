-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_inter_basicOpen_eq
-- name    : GroundTheory.Arith.SchemeCoh.inter_basicOpen_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:18:48.439682+00:00
-- url     : https://prove2.me/theorems/22e0b9c6-d8ce-4e82-9bc6-8e711a28637c
-- title:
--   Scheme Coh: inter basic Open eq
-- statement:
--   The Scheme Coh construction uses the inter basic Open eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwistLeray.lean#L182-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwistLeray.lean#L182-L192

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
variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]
open ProjTwist

theorem GroundTheory.Arith.SchemeCoh.inter_basicOpen_eq {ι : Type w} (v : ι → A) {m : ℕ} (i : Fin (m + 1) → ι) :
    inter (X := (Proj 𝒜).toTopCat) (fun j => Proj.basicOpen 𝒜 (v j)) i =
      Proj.basicOpen 𝒜 (∏ a, v (i a)) := by sorry
