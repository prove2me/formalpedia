-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_mem_equivariantFunctionals
-- name    : GroundTheory.Automorphic.Whittaker.mem_equivariantFunctionals
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:09:27.753717+00:00
-- url     : https://prove2.me/theorems/9697afe0-3e59-46aa-ba33-55070ea495e8
-- title:
--   Whittaker: mem equivariant Functionals
-- statement:
--   The Whittaker construction uses the mem equivariant Functionals property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L256-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCriterion.lean#L256-L259

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
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem GroundTheory.Automorphic.Whittaker.mem_equivariantFunctionals {ρ : Representation ℂ G V} {H : Subgroup G} {χ : H → ℂ}
    {ℓ : Module.Dual ℂ V} :
    ℓ ∈ equivariantFunctionals ρ χ ↔ ∀ h : H, ∀ v, ℓ (ρ h v) = χ h * ℓ v := by sorry
