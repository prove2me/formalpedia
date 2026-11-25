-- Prove2me | Theorems.Thm_GlobalTheory_T_characterTrivialMatrixLattice_open_compact_basis
-- name    : GlobalTheory.T.characterTrivialMatrixLattice_open_compact_basis
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:27:28.640285+00:00
-- url     : https://prove2.me/theorems/7372a1a0-d687-48d0-8377-816637ed1e68
-- title:
--   T: character Trivial Matrix Lattice open compact basis
-- statement:
--   The T construction uses the character Trivial Matrix Lattice open compact basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CharacterTrivialMatrixLatticeOpenCompactBasisStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CharacterTrivialMatrixLatticeOpenCompactBasisStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CharacterTrivialMatrixLatticeOpenCompactBasis
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AddCharNegEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CharacterTrivialMatrixLatticeOpenCompactBasisStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.characterTrivialMatrixLattice_open_compact_basis : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 → (∀ s : k, s ≠ 0 → IsOpen (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ∧ IsCompact (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k))) ∧ ∀ W ∈ 𝓝 (0 : Matrix (Fin n) (Fin d) k), ∃ s : k, s ≠ 0 ∧ (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ⊆ W := by sorry
