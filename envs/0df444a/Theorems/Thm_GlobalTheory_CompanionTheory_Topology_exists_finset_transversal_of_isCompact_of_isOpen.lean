-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Topology_exists_finset_transversal_of_isCompact_of_isOpen
-- name    : GlobalTheory.CompanionTheory.Topology.exists_finset_transversal_of_isCompact_of_isOpen
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:16:28.463774+00:00
-- url     : https://prove2.me/theorems/3c5f6704-8eb1-4409-a0f2-da728af6a9ee
-- title:
--   Topology: exists finset transversal of is Compact of is Open
-- statement:
--   The Topology construction uses the exists finset transversal of is Compact of is Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsCosetRepsOpenInCompact.lean#L6-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsCosetRepsOpenInCompact.lean#L6-L51

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCosetRepsOpenInCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Topology

theorem GlobalTheory.CompanionTheory.Topology.exists_finset_transversal_of_isCompact_of_isOpen
    (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (A L : AddSubgroup X) (hA : IsCompact (A : Set X)) (hL : IsOpen (L : Set X)) (_hLA : L ≤ A) :
    ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ (∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ L) := by sorry
