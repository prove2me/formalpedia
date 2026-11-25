-- Prove2me | Theorems.Thm_GlobalTheory_T_pDivCocycle_mem_range_cob_of_pullback_mulP
-- name    : GlobalTheory.T.pDivCocycle_mem_range_cob_of_pullback_mulP
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:10:54.900087+00:00
-- url     : https://prove2.me/theorems/93d9c723-0a51-5334-9880-014c138ca7f3
-- title:
--   T: p Div Cocycle mem range cob of pullback mul P
-- statement:
--   The T construction uses the p Div Cocycle mem range cob of pullback mul P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PDivCocycleMemRangeCobOfPullbackMulPStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PDivCocycleMemRangeCobOfPullbackMulPStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PDivCocycleMemRangeCobOfPullbackMulP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PDivCocycleMemRangeCobOfPullbackMulPStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.pDivCocycle_mem_range_cob_of_pullback_mulP : ∀ {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (G : PDivGroup p R) (c : G.cocycles) (B : G.funs), G.cob B = cocyclesMap ((p : ℤ_[p]) • 𝟙 G) c → B.1 1 = 0 → c ∈ LinearMap.range G.cob := by sorry
