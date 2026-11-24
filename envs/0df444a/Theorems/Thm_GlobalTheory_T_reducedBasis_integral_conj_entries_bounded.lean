-- Prove2me | Theorems.Thm_GlobalTheory_T_reducedBasis_integral_conj_entries_bounded
-- name    : GlobalTheory.T.reducedBasis_integral_conj_entries_bounded
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:56:31.21805+00:00
-- url     : https://prove2.me/theorems/8aed3a0d-1bb7-47b3-a484-d815cd2fd2f5
-- title:
--   T: reduced Basis integral conj entries bounded
-- statement:
--   The T construction uses the reduced Basis integral conj entries bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ReducedBasisIntegralConjEntriesBoundedStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ReducedBasisIntegralConjEntriesBoundedStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ReducedBasisIntegralConjEntriesBounded
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ReducedBasisIntegralConjEntriesBoundedStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.reducedBasis_integral_conj_entries_bounded : ∀ (N : ℕ) (C R : ℝ), ∃ C' : ℝ, ∀ (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ), IsSiegel C k a n → ∀ (X : Matrix (Fin N) (Fin N) ℝ) (M M' : Matrix (Fin N) (Fin N) ℤ), (∀ i j, |X i j| ≤ R) → (k * diagonal a * n) * M.map (Int.cast : ℤ → ℝ) = X * (k * diagonal a * n) → (k * diagonal a * n) * M'.map (Int.cast : ℤ → ℝ) = Xᵀ * (k * diagonal a * n) → ∀ i j, |(M i j : ℝ)| ≤ C' := by sorry
