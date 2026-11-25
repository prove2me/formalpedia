-- Prove2me | Theorems.Thm_GlobalTheory_T_bialgebraPullbackTwo_convMul_symmetricCocycle
-- name    : GlobalTheory.T.bialgebraPullbackTwo_convMul_symmetricCocycle
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:11:05.61267+00:00
-- url     : https://prove2.me/theorems/6950e64d-176e-5afe-841d-8380464823e9
-- title:
--   T: bialgebra Pullback Two conv Mul symmetric Cocycle
-- statement:
--   The T construction uses the bialgebra Pullback Two conv Mul symmetric Cocycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BialgebraPullbackTwoConvMulSymmetricCocycleStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BialgebraPullbackTwoConvMulSymmetricCocycleStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BialgebraPullbackTwoConvMulSymmetricCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BialgebraPullbackTwoConvMulSymmetricCocycleStatement
import Theorems.Thm_GlobalTheory_IsBicharacter_map

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

theorem GlobalTheory.T.bialgebraPullbackTwo_convMul_symmetricCocycle : ∀ {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B] [IsCocomm R A] (f g : A →ₐc[R] B) (c : A ⊗[R] A), c ∈ symCocycles R A → pullbackTwo (toConv f * toConv g).ofConv c = pullbackTwo f c + pullbackTwo g c + cobOne R B (LinearMap.mul' R B (TensorProduct.map (f : A →ₗ[R] B) (g : A →ₗ[R] B) c)) := by sorry
