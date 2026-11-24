-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MatrixRowSpace_span_rows_mul
-- name    : GlobalTheory.CompanionTheory.MatrixRowSpace.span_rows_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:53:07.944923+00:00
-- url     : https://prove2.me/theorems/f88b6f12-ac67-4d07-9ddc-28742fb3a6ed
-- title:
--   Matrix Row Space: span rows mul
-- statement:
--   The Matrix Row Space construction uses the span rows mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RangeVecMulLinearEq.lean#L24-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RangeVecMulLinearEq.lean#L24-L35

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

theorem GlobalTheory.CompanionTheory.MatrixRowSpace.span_rows_mul {m n r : ℕ} (x : Matrix (Fin m) (Fin r) K) (c : Matrix (Fin r) (Fin n) K) :
    Submodule.span K (Set.range (x * c)) =
      (Submodule.span K (Set.range x)).map c.vecMulLinear := by sorry
