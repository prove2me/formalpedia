-- Prove2me | Theorems.Thm_GlobalTheory_topologicalKrullDim_eq_of_forall_exists_isOpen
-- name    : GlobalTheory.topologicalKrullDim_eq_of_forall_exists_isOpen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:55:00.104035+00:00
-- url     : https://prove2.me/theorems/c4f552ce-71a7-49c5-b34b-cc0fb85d04c5
-- title:
--   Global Theory: topological Krull Dim eq of forall exists is Open
-- statement:
--   The Global Theory construction uses the topological Krull Dim eq of forall exists is Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RingKrullDimQuotientEqOfMemMinimalPrimes.lean#L341-L356
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/RingKrullDimQuotientEqOfMemMinimalPrimes.lean#L341-L356

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing
open GlobalTheory
universe u
open Topology TopologicalSpace

theorem GlobalTheory.topologicalKrullDim_eq_of_forall_exists_isOpen {X : Type*} [TopologicalSpace X]
    {Z : Set X} (hZ : Z.Nonempty) {d : WithBot ℕ∞}
    (h : ∀ x ∈ Z, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ topologicalKrullDim (U ∩ Z : Set X) = d) :
    topologicalKrullDim Z = d := by sorry
