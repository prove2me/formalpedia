-- Prove2me | Theorems.Thm_GlobalTheory_T_lattice_multiple_mem_sublattice
-- name    : GlobalTheory.T.lattice_multiple_mem_sublattice
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:34:31.220895+00:00
-- url     : https://prove2.me/theorems/995055e9-a03f-5b67-91f9-dd511dfee801
-- title:
--   T: lattice multiple mem sublattice
-- statement:
--   The T construction uses the lattice multiple mem sublattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeMultipleMemSublatticeStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeMultipleMemSublatticeStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeMultipleMemSublattice
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeMultipleMemSublatticeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.lattice_multiple_mem_sublattice : ∀ (n : ℕ) (Λ Λ₂ M : Submodule ℤ (Fin n → ℂ)), DiscreteTopology Λ → DiscreteTopology Λ₂ → Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤ → Submodule.span ℝ (Λ₂ : Set (Fin n → ℂ)) = ⊤ → M ≤ Λ → Module.rank ℤ Λ₂ ≤ Module.rank ℤ M → ∀ w ∈ Λ, ∃ k : ℤ, k ≠ 0 ∧ k • w ∈ M := by sorry
