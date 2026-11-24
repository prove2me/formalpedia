-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MatrixRowSpace_row_mul
-- name    : GlobalTheory.CompanionTheory.MatrixRowSpace.row_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:53:01.332054+00:00
-- url     : https://prove2.me/theorems/2d08e7ee-962a-42f1-969e-8395d1a9776f
-- title:
--   Matrix Row Space: row mul
-- statement:
--   The Matrix Row Space construction uses the row mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RangeVecMulLinearEq.lean#L7-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RangeVecMulLinearEq.lean#L7-L10

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RangeVecMulLinearEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MatrixRowSpace
variable {K : Type} [Field K]

theorem GlobalTheory.CompanionTheory.MatrixRowSpace.row_mul {m n r : ℕ} (x : Matrix (Fin m) (Fin r) K) (c : Matrix (Fin r) (Fin n) K)
    (i : Fin m) : (x * c) i = c.vecMulLinear (x i) := by sorry
