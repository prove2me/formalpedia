-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_GL_mul_rightColumns_eq_zero_of_rank
-- name    : GlobalTheory.T.exists_GL_mul_rightColumns_eq_zero_of_rank
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:31.457038+00:00
-- url     : https://prove2.me/theorems/7dd8d316-2fa7-4751-acac-05d8243d9a29
-- title:
--   T: exists GL mul right Columns eq zero of rank
-- statement:
--   The T construction uses the exists GL mul right Columns eq zero of rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsGLMulRightColumnsEqZeroOfRankStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsGLMulRightColumnsEqZeroOfRankStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsGLMulRightColumnsEqZeroOfRank
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsGLMulRightColumnsEqZeroOfRankStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_GL_mul_rightColumns_eq_zero_of_rank : ∀ (k m a b n : Type) [Field k] [Fintype m] [Fintype a] [Fintype b] [Fintype n] [DecidableEq n] (e : a ⊕ b ≃ n) (x : Matrix m n k), x.rank = Fintype.card a → ∃ g : GL n k, ∀ i j, (x * g.val) i (e (Sum.inr j)) = 0 := by sorry
