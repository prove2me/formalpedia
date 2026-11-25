-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_open_compact_lattice_containing
-- name    : GlobalTheory.T.exists_open_compact_lattice_containing
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:30:35.451402+00:00
-- url     : https://prove2.me/theorems/cbe22a59-fd98-4a33-9055-18368feb566d
-- title:
--   T: exists open compact lattice containing
-- statement:
--   The T construction uses the exists open compact lattice containing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOpenCompactLatticeContainingStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOpenCompactLatticeContainingStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOpenCompactLatticeContaining
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOpenCompactLatticeContainingStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_open_compact_lattice_containing : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (K : Set (Fin n → k)), IsCompact K → ∃ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) ∧ IsOpen (A : Set (Fin n → k)) ∧ K ⊆ A := by sorry
