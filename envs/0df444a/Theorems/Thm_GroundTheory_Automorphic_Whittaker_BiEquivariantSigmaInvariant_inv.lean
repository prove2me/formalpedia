-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_BiEquivariantSigmaInvariant_inv
-- name    : GroundTheory.Automorphic.Whittaker.BiEquivariantSigmaInvariant.inv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:02:01.639039+00:00
-- url     : https://prove2.me/theorems/108affce-c4b2-4930-853c-bad1e15eb030
-- title:
--   Bi Equivariant Sigma Invariant: inv
-- statement:
--   The Bi Equivariant Sigma Invariant construction uses the inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L92-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L92-L116

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Filter Topology MeasureTheory
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem GroundTheory.Automorphic.Whittaker.BiEquivariantSigmaInvariant.inv {H : Subgroup G} {χ : H → ℂ} {σ : G ≃ₜ G}
    (hσ : ∀ x y, σ (x * y) = σ y * σ x) (h : BiEquivariantSigmaInvariant H χ σ) :
    BiEquivariantSigmaInvariant H (fun g => (χ g)⁻¹) σ := by sorry
