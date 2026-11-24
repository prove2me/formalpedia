-- Prove2me | Theorems.Thm_GlobalTheory_sublattice_of_full_rank_quotient_torsion
-- name    : GlobalTheory.sublattice_of_full_rank_quotient_torsion
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:21:34.946864+00:00
-- url     : https://prove2.me/theorems/d6fb56bb-fb91-41af-bf81-730133a472bf
-- title:
--   Global Theory: sublattice of full rank quotient torsion
-- statement:
--   The Global Theory construction uses the sublattice of full rank quotient torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeMultipleMemSublattice.lean#L7-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeMultipleMemSublattice.lean#L7-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeMultipleMemSublattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory

theorem GlobalTheory.sublattice_of_full_rank_quotient_torsion : ∀ (n : ℕ) (Λ Λ₂ M : Submodule ℤ (Fin n → ℂ)), DiscreteTopology Λ → DiscreteTopology Λ₂ → Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤ → Submodule.span ℝ (Λ₂ : Set (Fin n → ℂ)) = ⊤ → M ≤ Λ → Module.rank ℤ Λ₂ ≤ Module.rank ℤ M → ∀ w ∈ Λ, ∃ k : ℤ, k ≠ 0 ∧ k • w ∈ M := by sorry
