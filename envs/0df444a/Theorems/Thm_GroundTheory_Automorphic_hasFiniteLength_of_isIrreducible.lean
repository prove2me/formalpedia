-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_hasFiniteLength_of_isIrreducible
-- name    : GroundTheory.Automorphic.hasFiniteLength_of_isIrreducible
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:47:22.678865+00:00
-- url     : https://prove2.me/theorems/5b2c39be-5b83-4d93-a9b3-02ac57074fd7
-- title:
--   Automorphic: has Finite Length of is Irreducible
-- statement:
--   The Automorphic construction uses the has Finite Length of is Irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteLengthLattice.lean#L49-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteLengthLattice.lean#L49-L53

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

theorem GroundTheory.Automorphic.hasFiniteLength_of_isIrreducible [ρ.IsIrreducible] : HasFiniteLength ρ := by sorry
