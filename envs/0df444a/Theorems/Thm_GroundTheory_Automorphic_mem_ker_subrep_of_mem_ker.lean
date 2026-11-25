-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_mem_ker_subrep_of_mem_ker
-- name    : GroundTheory.Automorphic.mem_ker_subrep_of_mem_ker
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:56:58.100016+00:00
-- url     : https://prove2.me/theorems/37b0c2bd-61ff-4baf-b58d-71dedd930e56
-- title:
--   Automorphic: mem ker subrep of mem ker
-- statement:
--   The Automorphic construction uses the mem ker subrep of mem ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteLengthSubquotient.lean#L212-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteLengthSubquotient.lean#L212-L244

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthLattice
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthSubquotient
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
open Function Parabolic
universe u
variable {G : Type*} [Group G] [TopologicalSpace G] {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V}
variable [IsTopologicalGroup G]

theorem GroundTheory.Automorphic.mem_ker_subrep_of_mem_ker (N : Subgroup G) [LocallyCompactSpace N] [T2Space N]
    [TotallyDisconnectedSpace N]
    (hN : ∀ s : Finset N, ∃ K : Subgroup N, IsCompact (K : Set N) ∧ IsOpen (K : Set N) ∧
      ∀ x ∈ s, x ∈ K)
    (hρ : IsSmooth ρ) (C : Subrepresentation ρ) {c : C.toSubmodule}
    (hc : (c : V) ∈ Representation.Coinvariants.ker (ρ.comp N.subtype)) :
    c ∈ Representation.Coinvariants.ker (C.toRepresentation.comp N.subtype) := by sorry
