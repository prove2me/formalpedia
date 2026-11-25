-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_hasFiniteLength_of_surjective
-- name    : GroundTheory.Automorphic.hasFiniteLength_of_surjective
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:24:50.557948+00:00
-- url     : https://prove2.me/theorems/59857a75-78be-4af2-baaa-eb210575aea6
-- title:
--   Automorphic: has Finite Length of surjective
-- statement:
--   The Automorphic construction uses the has Finite Length of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteLengthLattice.lean#L96-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteLengthLattice.lean#L96-L108

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Function
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {ρ : Representation ℂ G V}
variable {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W}

theorem GroundTheory.Automorphic.hasFiniteLength_of_surjective (f : Representation.IntertwiningMap ρ σ)
    (hf : Surjective f) (hρ : HasFiniteLength ρ) : HasFiniteLength σ := by sorry
