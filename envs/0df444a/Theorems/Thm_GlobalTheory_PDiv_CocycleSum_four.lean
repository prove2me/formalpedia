-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_CocycleSum_four
-- name    : GlobalTheory.PDiv.CocycleSum.four
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:47:09.319992+00:00
-- url     : https://prove2.me/theorems/e54f0ecd-fd58-51e9-9ba7-dcab250d28ea
-- title:
--   Cocycle Sum: four
-- statement:
--   The Cocycle Sum construction uses the four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BialgebraPullbackTwoConvMulSymmetricCocycle.lean#L16-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BialgebraPullbackTwoConvMulSymmetricCocycle.lean#L16-L31

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

theorem GlobalTheory.PDiv.CocycleSum.four {M N : Type} [CommMonoid M] [AddCommGroup N] (c : M → M → N)
    (h : ∀ x y z, c y z - c (x * y) z + c x (y * z) - c x y = 0) (hs : ∀ x y, c x y = c y x)
    (a b a' b' : M) :
    c (a * b) (a' * b') = c a a' + c b b' + (c (a * a') (b * b') - c a b - c a' b') := by sorry
