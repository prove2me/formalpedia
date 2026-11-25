-- Prove2me | Theorems.Thm_GlobalTheory_T_lattice_annihilator_within_nhds
-- name    : GlobalTheory.T.lattice_annihilator_within_nhds
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:34:21.36628+00:00
-- url     : https://prove2.me/theorems/b6c0b7a1-2700-5df6-a98d-e630cf82f5a5
-- title:
--   T: lattice annihilator within nhds
-- statement:
--   The T construction uses the lattice annihilator within nhds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticeAnnihilatorWithinNhdsStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LatticeAnnihilatorWithinNhdsStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticeAnnihilatorWithinNhds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticeAnnihilatorWithinNhdsStatement
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

theorem GlobalTheory.T.lattice_annihilator_within_nhds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (U : Set (Fin n → k)), U ∈ nhds (0 : Fin n → k) → ∃ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) ∧ IsOpen (A : Set (Fin n → k)) ∧ {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} ⊆ U := by sorry
