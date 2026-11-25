-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_character_separating_lattice
-- name    : GlobalTheory.T.exists_character_separating_lattice
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:29:03.486594+00:00
-- url     : https://prove2.me/theorems/729c69a1-a5ac-5703-8152-f42691f89a47
-- title:
--   T: exists character separating lattice
-- statement:
--   The T construction uses the exists character separating lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsCharacterSeparatingLatticeStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsCharacterSeparatingLatticeStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCharacterSeparatingLattice
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCharacterSeparatingLatticeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_character_separating_lattice : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (A : AddSubgroup (Fin n → k)), IsCompact (A : Set (Fin n → k)) → IsOpen (A : Set (Fin n → k)) → ∀ x : Fin n → k, x ∉ A → ∃ η : Fin n → k, (∀ a ∈ A, ψ (η ⬝ᵥ a) = 1) ∧ ψ (η ⬝ᵥ x) ≠ 1 := by sorry
