-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_CocycleSum_mul_apply
-- name    : GlobalTheory.PDiv.CocycleSum.mul_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:46:55.297699+00:00
-- url     : https://prove2.me/theorems/10f07f28-f36c-438b-b196-05a62330072e
-- title:
--   Cocycle Sum: mul apply
-- statement:
--   The Cocycle Sum construction uses the mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BialgebraPullbackTwoConvMulSymmetricCocycle.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BialgebraPullbackTwoConvMulSymmetricCocycle.lean#L41-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BialgebraPullbackTwoConvMulSymmetricCocycle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv
open GlobalTheory
open GlobalTheory.PDiv
open GlobalTheory.PDiv.CocycleSum
variable {R A X : Type} [CommRing R] [CommRing A] [CommRing X] [Bialgebra R A] [Algebra R X]

theorem GlobalTheory.PDiv.CocycleSum.mul_apply (x y : WithConv (A →ₐ[R] X)) (a : A) :
    (x * y).ofConv a = val x y (comul a) := by sorry
