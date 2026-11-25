-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_pullback_mulP_of_pTorsion_invariant
-- name    : GlobalTheory.T.exists_pullback_mulP_of_pTorsion_invariant
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:34:48.085523+00:00
-- url     : https://prove2.me/theorems/e410711a-3b46-4028-86ac-0f7e1b1934b0
-- title:
--   T: exists pullback mul P of p Torsion invariant
-- statement:
--   The T construction uses the exists pullback mul P of p Torsion invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPullbackMulPOfPTorsionInvariantStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPullbackMulPOfPTorsionInvariantStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPullbackMulPOfPTorsionInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPullbackMulPOfPTorsionInvariantStatement
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

theorem GlobalTheory.T.exists_pullback_mulP_of_pTorsion_invariant : ∀ {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ) (F : G.A (n + 1) ⊗[R] G.A (n + 1)), ((G.transl n).toLinearMap - (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).rTensor (G.A (n + 1)) F = 0 → ((G.transl n).toLinearMap - (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).lTensor (G.A (n + 1)) F = 0 → ∃ c : G.A n ⊗[R] G.A n, pullbackTwo (G.mulP n) c = F := by sorry
