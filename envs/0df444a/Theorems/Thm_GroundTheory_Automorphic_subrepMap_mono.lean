-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_subrepMap_mono
-- name    : GroundTheory.Automorphic.subrepMap_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:39.916948+00:00
-- url     : https://prove2.me/theorems/3768002b-6bb1-458e-9246-08ae9f191e27
-- title:
--   Automorphic: subrep Map mono
-- statement:
--   The Automorphic construction uses the subrep Map mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteLengthLattice.lean#L74-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteLengthLattice.lean#L74-L75

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

theorem GroundTheory.Automorphic.subrepMap_mono (f : Representation.IntertwiningMap ρ σ) : Monotone (subrepMap f) := by sorry
