-- Prove2me | Theorems.Thm_GlobalTheory_exists_gl_mul_cols_eq_zero_of_rank
-- name    : GlobalTheory.exists_gl_mul_cols_eq_zero_of_rank
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:32:58.71884+00:00
-- url     : https://prove2.me/theorems/25374e5f-a9ab-415d-bdd7-e448c565d29e
-- title:
--   Global Theory: exists gl mul cols eq zero of rank
-- statement:
--   The Global Theory construction uses the exists gl mul cols eq zero of rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsGLMulRightColumnsEqZeroOfRank.lean#L7-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsGLMulRightColumnsEqZeroOfRank.lean#L7-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsGLMulRightColumnsEqZeroOfRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology
open GlobalTheory

theorem GlobalTheory.exists_gl_mul_cols_eq_zero_of_rank (k m a b n : Type) [Field k] [Fintype m] [Fintype a]
    [Fintype b] [Fintype n] [DecidableEq n] (e : a ⊕ b ≃ n) (x : Matrix m n k)
    (hx : x.rank = Fintype.card a) :
    ∃ g : GL n k, ∀ i j, (x * g.val) i (e (Sum.inr j)) = 0 := by sorry
