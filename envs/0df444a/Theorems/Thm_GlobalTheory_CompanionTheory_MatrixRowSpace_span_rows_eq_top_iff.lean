-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MatrixRowSpace_span_rows_eq_top_iff
-- name    : GlobalTheory.CompanionTheory.MatrixRowSpace.span_rows_eq_top_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:53:13.464432+00:00
-- url     : https://prove2.me/theorems/e92e7a7c-2f00-4b3c-94de-00cde325270c
-- title:
--   Matrix Row Space: span rows eq top iff
-- statement:
--   The Matrix Row Space construction uses the span rows eq top iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RangeVecMulLinearEq.lean#L37-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RangeVecMulLinearEq.lean#L37-L46

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

theorem GlobalTheory.CompanionTheory.MatrixRowSpace.span_rows_eq_top_iff {m r : ℕ} (x : Matrix (Fin m) (Fin r) K) :
    x.rank = r ↔ Submodule.span K (Set.range x) = ⊤ := by sorry
