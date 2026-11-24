-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MatrixRowSpace_range_vecMulLinear_eq
-- name    : GlobalTheory.CompanionTheory.MatrixRowSpace.range_vecMulLinear_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:53:07.865824+00:00
-- url     : https://prove2.me/theorems/f6d85837-5c13-44bc-9143-0f08d0d2775f
-- title:
--   Matrix Row Space: range vec Mul Linear eq
-- statement:
--   The Matrix Row Space construction uses the range vec Mul Linear eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RangeVecMulLinearEq.lean#L12-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RangeVecMulLinearEq.lean#L12-L22

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

theorem GlobalTheory.CompanionTheory.MatrixRowSpace.range_vecMulLinear_eq {n r : ℕ} (c : Matrix (Fin r) (Fin n) K) :
    LinearMap.range c.vecMulLinear = Submodule.span K (Set.range c) := by sorry
