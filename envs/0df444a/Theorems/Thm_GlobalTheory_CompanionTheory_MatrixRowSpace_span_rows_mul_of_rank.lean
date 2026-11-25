-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MatrixRowSpace_span_rows_mul_of_rank
-- name    : GlobalTheory.CompanionTheory.MatrixRowSpace.span_rows_mul_of_rank
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:01:23.783915+00:00
-- url     : https://prove2.me/theorems/cdfa9039-c0f3-5cc0-99b3-7988db0d6077
-- title:
--   Matrix Row Space: span rows mul of rank
-- statement:
--   The Matrix Row Space construction uses the span rows mul of rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RangeVecMulLinearEq.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RangeVecMulLinearEq.lean#L48-L51

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

theorem GlobalTheory.CompanionTheory.MatrixRowSpace.span_rows_mul_of_rank {m n r : ℕ} (x : Matrix (Fin m) (Fin r) K)
    (c : Matrix (Fin r) (Fin n) K) (hx : x.rank = r) :
    Submodule.span K (Set.range (x * c)) = Submodule.span K (Set.range c) := by sorry
