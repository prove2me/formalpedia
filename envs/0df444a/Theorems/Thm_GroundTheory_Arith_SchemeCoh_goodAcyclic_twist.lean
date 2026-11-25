-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_goodAcyclic_twist
-- name    : GroundTheory.Arith.SchemeCoh.goodAcyclic_twist
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:10:21.628237+00:00
-- url     : https://prove2.me/theorems/a1630924-27aa-4183-87a9-77cc2c96f864
-- title:
--   Scheme Coh: good Acyclic twist
-- statement:
--   The Scheme Coh construction uses the good Acyclic twist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwistLeray.lean#L165-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwistLeray.lean#L165-L180

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

theorem GroundTheory.Arith.SchemeCoh.goodAcyclic_twist {ι : Type w} (v : ι → A) (hv : ∀ j, v j ∈ 𝒜 1) (k : ℤ) :
    GoodAcyclic (X := (Proj 𝒜).toTopCat) (AffineUnder v)
      (fun {κ} V U => IsBasicCover (κ := κ) V U ∧ AffineUnder v V)
      (modulesAb (twistingSheaf 𝒜 k)) := by sorry
