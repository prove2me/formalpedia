-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_hasFiniteLength_of_injective
-- name    : GroundTheory.Automorphic.hasFiniteLength_of_injective
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:49:41.527503+00:00
-- url     : https://prove2.me/theorems/7a49040c-e609-4a7a-8889-f73e1182e895
-- title:
--   Automorphic: has Finite Length of injective
-- statement:
--   The Automorphic construction uses the has Finite Length of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteLengthLattice.lean#L80-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteLengthLattice.lean#L80-L94

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

theorem GroundTheory.Automorphic.hasFiniteLength_of_injective (f : Representation.IntertwiningMap ρ σ)
    (hf : Injective f) (hσ : HasFiniteLength σ) : HasFiniteLength ρ := by sorry
