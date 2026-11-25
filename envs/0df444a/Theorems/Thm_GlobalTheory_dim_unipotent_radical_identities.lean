-- Prove2me | Theorems.Thm_GlobalTheory_dim_unipotent_radical_identities
-- name    : GlobalTheory.dim_unipotent_radical_identities
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:44:52.15542+00:00
-- url     : https://prove2.me/theorems/5a311bf9-1cf6-4dbc-afa2-c323af6417b6
-- title:
--   Global Theory: dim unipotent radical identities
-- statement:
--   The Global Theory construction uses the dim unipotent radical identities property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SqSumEqSumSqAddTwoMulSumLt.lean#L30-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SqSumEqSumSqAddTwoMulSumLt.lean#L30-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SqSumEqSumSqAddTwoMulSumLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Real
open GlobalTheory
open Matrix Finset Real

theorem GlobalTheory.dim_unipotent_radical_identities :
    ∀ (a : ℕ) (j : Fin a → ℤ) (n : ℤ), let J := ∑ i, j i; let n₀ := n - 2 * J; let dimN := 4 * (∑ i, ∑ k, if i < k then j i * j k else 0) + 2 * J * n₀ + ∑ i, j i ^ 2; dimN = 2 * J ^ 2 - ∑ i, j i ^ 2 + 2 * J * n₀ ∧ n ^ 2 = n₀ ^ 2 + 2 * ∑ i, j i ^ 2 + 2 * dimN ∧ dimN ≤ 2 * J * n := by sorry
