-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_CocycleSum_lift_cobTwo
-- name    : GlobalTheory.PDiv.CocycleSum.lift_cobTwo
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:47:53.394683+00:00
-- url     : https://prove2.me/theorems/41a3f85d-f5d8-4a62-94ab-50e7bb76cfe9
-- title:
--   Cocycle Sum: lift cob Two
-- statement:
--   The Cocycle Sum construction uses the lift cob Two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BialgebraPullbackTwoConvMulSymmetricCocycle.lean#L46-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BialgebraPullbackTwoConvMulSymmetricCocycle.lean#L46-L66

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

theorem GlobalTheory.PDiv.CocycleSum.lift_cobTwo (x y z : WithConv (A →ₐ[R] X)) (c : A ⊗[R] A) :
    Algebra.TensorProduct.lift x.ofConv (val y z) (fun _ _ => .all ..) (cobTwo R A c) =
      val y z c - val (x * y) z c + val x (y * z) c - val x y c := by sorry
