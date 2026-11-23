-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_hasFiniteLength_iff
-- name    : GroundTheory.Automorphic.hasFiniteLength_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:53.474135+00:00
-- url     : https://prove2.me/theorems/6402ef96-f81a-4011-b733-acce0d51637d
-- title:
--   Automorphic: has Finite Length iff
-- statement:
--   The Automorphic construction uses the has Finite Length iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteLengthLattice.lean#L17-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteLengthLattice.lean#L17-L26

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

theorem GroundTheory.Automorphic.hasFiniteLength_iff :
    HasFiniteLength ρ ↔
      WellFoundedLT (Subrepresentation ρ) ∧ WellFoundedGT (Subrepresentation ρ) := by sorry
