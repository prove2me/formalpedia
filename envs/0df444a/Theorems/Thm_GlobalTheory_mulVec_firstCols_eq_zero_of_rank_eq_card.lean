-- Prove2me | Theorems.Thm_GlobalTheory_mulVec_firstCols_eq_zero_of_rank_eq_card
-- name    : GlobalTheory.mulVec_firstCols_eq_zero_of_rank_eq_card
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:13:00.337621+00:00
-- url     : https://prove2.me/theorems/22b20c52-efa4-4cf4-9a27-845362cf78c4
-- title:
--   Global Theory: mul Vec first Cols eq zero of rank eq card
-- statement:
--   The Global Theory construction uses the mul Vec first Cols eq zero of rank eq card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftColumnsMulVecInjectiveOfRankEqCard.lean#L9-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftColumnsMulVecInjectiveOfRankEqCard.lean#L9-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftColumnsMulVecInjectiveOfRankEqCard
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
open Matrix Topology Module

theorem GlobalTheory.mulVec_firstCols_eq_zero_of_rank_eq_card :
    ∀ (k m a b n : Type) [Field k] [Fintype m] [Fintype a] [Fintype b] [Fintype n] (e : a ⊕ b ≃ n) (x : Matrix m n k), x.rank = Fintype.card a → (∀ i j, x i (e (Sum.inr j)) = 0) → ∀ v : a → k, (x.submatrix id (fun i => e (Sum.inl i))) *ᵥ v = 0 → v = 0 := by sorry
