-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_hasFiniteLength_of_strictMono
-- name    : GroundTheory.Automorphic.hasFiniteLength_of_strictMono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:56.37821+00:00
-- url     : https://prove2.me/theorems/a7619700-ec26-43bb-bc16-a81add4b29c8
-- title:
--   Automorphic: has Finite Length of strict Mono
-- statement:
--   The Automorphic construction uses the has Finite Length of strict Mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteLengthLattice.lean#L36-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteLengthLattice.lean#L36-L43

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

theorem GroundTheory.Automorphic.hasFiniteLength_of_strictMono {ι : Type*} [Finite ι] {α : ι → Type*}
    [∀ i, PartialOrder (α i)] [∀ i, WellFoundedLT (α i)] [∀ i, WellFoundedGT (α i)]
    (Λ : Subrepresentation ρ → ∀ i, α i) (hΛ : StrictMono Λ) : HasFiniteLength ρ := by sorry
