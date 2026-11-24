-- Prove2me | Theorems.Thm_GlobalTheory_T_unipotent_upper_size_reduction
-- name    : GlobalTheory.T.unipotent_upper_size_reduction
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:00:50.094112+00:00
-- url     : https://prove2.me/theorems/644f67c9-c4c6-4180-9a46-ca76124cd9ee
-- title:
--   T: unipotent upper size reduction
-- statement:
--   The T construction uses the unipotent upper size reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/UnipotentUpperSizeReductionStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/UnipotentUpperSizeReductionStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnipotentUpperSizeReduction
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnipotentUpperSizeReductionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.unipotent_upper_size_reduction : ∀ (N : ℕ) (n : Matrix (Fin N) (Fin N) ℝ), (∀ i, n i i = 1) → (∀ i j, j < i → n i j = 0) → ∃ ν : Matrix (Fin N) (Fin N) ℤ, (∀ i, ν i i = 1) ∧ (∀ i j, j < i → ν i j = 0) ∧ ∀ i j, i < j → |(n * ν.map (Int.cast : ℤ → ℝ)) i j| ≤ 1 / 2 := by sorry
