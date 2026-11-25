-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_exists_tensorSquare_mulP_eq
-- name    : GlobalTheory.PDivGroup.exists_tensorSquare_mulP_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:50:36.716089+00:00
-- url     : https://prove2.me/theorems/0fccca01-3f3f-5778-bc90-a4922a04c7d0
-- title:
--   PDiv Group: exists tensor Square mul P eq
-- statement:
--   The PDiv Group construction uses the exists tensor Square mul P eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPullbackMulPOfPTorsionInvariant.lean#L25-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPullbackMulPOfPTorsionInvariant.lean#L25-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulPEqOfTranslInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPullbackMulPOfPTorsionInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
open GlobalTheory

theorem GlobalTheory.PDivGroup.exists_tensorSquare_mulP_eq {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)
    (n : ℕ) (F : G.A (n + 1) ⊗[R] G.A (n + 1))
    (h₁ : ((G.transl n).toLinearMap -
      (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).rTensor (G.A (n + 1)) F = 0)
    (h₂ : ((G.transl n).toLinearMap -
      (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).lTensor (G.A (n + 1)) F = 0) :
    ∃ c : G.A n ⊗[R] G.A n, pullbackTwo (G.mulP n) c = F := by sorry
