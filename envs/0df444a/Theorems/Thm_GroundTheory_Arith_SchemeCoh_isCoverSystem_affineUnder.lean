-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_isCoverSystem_affineUnder
-- name    : GroundTheory.Arith.SchemeCoh.isCoverSystem_affineUnder
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:19:55.851594+00:00
-- url     : https://prove2.me/theorems/f99fea40-8465-443e-8bd5-ad27446fc75e
-- title:
--   Scheme Coh: is Cover System affine Under
-- statement:
--   The Scheme Coh construction uses the is Cover System affine Under property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwistLeray.lean#L152-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwistLeray.lean#L152-L163

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

theorem GroundTheory.Arith.SchemeCoh.isCoverSystem_affineUnder {ι : Type w} (v : ι → A) :
    IsCoverSystem (X := (Proj 𝒜).toTopCat) (AffineUnder v)
      (fun {κ} V U => IsBasicCover (κ := κ) V U ∧ AffineUnder v V) := by sorry
