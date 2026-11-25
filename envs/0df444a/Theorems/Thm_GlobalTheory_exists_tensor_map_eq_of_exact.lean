-- Prove2me | Theorems.Thm_GlobalTheory_exists_tensor_map_eq_of_exact
-- name    : GlobalTheory.exists_tensor_map_eq_of_exact
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:49:55.719023+00:00
-- url     : https://prove2.me/theorems/6636e029-ce15-4e4a-9e6e-ab6b215de521
-- title:
--   Global Theory: exists tensor map eq of exact
-- statement:
--   The Global Theory construction uses the exists tensor map eq of exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPullbackMulPOfPTorsionInvariant.lean#L11-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPullbackMulPOfPTorsionInvariant.lean#L11-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulPEqOfTranslInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPullbackMulPOfPTorsionInvariant
import Theorems.Thm_GlobalTheory_IsBicharacter_map

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

theorem GlobalTheory.exists_tensor_map_eq_of_exact {R M N P : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] [Module.Flat R M]
    [Module.Flat R N] [Module.Flat R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : Function.Injective f) (h : Function.Exact f g) (F : N ⊗[R] N)
    (h₁ : g.rTensor N F = 0) (h₂ : g.lTensor N F = 0) :
    ∃ c : M ⊗[R] M, TensorProduct.map f f c = F := by sorry
