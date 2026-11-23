-- Prove2me | Theorems.Thm_GlobalTheory_T_leftColumns_mulVec_injective_of_rank_eq_card
-- name    : GlobalTheory.T.leftColumns_mulVec_injective_of_rank_eq_card
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:59.678302+00:00
-- url     : https://prove2.me/theorems/3427c7b3-1435-43b6-a8fe-a6090743b64c
-- title:
--   T: left Columns mul Vec injective of rank eq card
-- statement:
--   The T construction uses the left Columns mul Vec injective of rank eq card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftColumnsMulVecInjectiveOfRankEqCardStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftColumnsMulVecInjectiveOfRankEqCardStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftColumnsMulVecInjectiveOfRankEqCard
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftColumnsMulVecInjectiveOfRankEqCardStatement
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

theorem GlobalTheory.T.leftColumns_mulVec_injective_of_rank_eq_card : ∀ (k m a b n : Type) [Field k] [Fintype m] [Fintype a] [Fintype b] [Fintype n] (e : a ⊕ b ≃ n) (x : Matrix m n k), x.rank = Fintype.card a → (∀ i j, x i (e (Sum.inr j)) = 0) → ∀ v : a → k, (x.submatrix id (fun i => e (Sum.inl i))) *ᵥ v = 0 → v = 0 := by sorry
