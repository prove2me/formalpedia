-- Prove2me | Theorems.Thm_GlobalTheory_sq_quadraticGaussSum
-- name    : GlobalTheory.sq_quadraticGaussSum
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:21:42.677232+00:00
-- url     : https://prove2.me/theorems/0439c140-bde8-4010-8243-13284990f361
-- title:
--   Global Theory: sq quadratic Gauss Sum
-- statement:
--   The Global Theory construction uses the sq quadratic Gauss Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRepresentativesQuotientRangeMulVecLin.lean#L214-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsRepresentativesQuotientRangeMulVecLin.lean#L214-L220

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open GlobalTheory
variable {A : Type*} [AddCommGroup A] [Fintype A]

theorem GlobalTheory.sq_quadraticGaussSum (hodd : Odd (Fintype.card A))
    (q : QuadraticMap ℤ A (AddCircle (1 : ℚ)))
    (hnd : ∀ x, (∀ y, QuadraticMap.polar q x y = 0) → x = 0) :
    (∑ x, ratCircleChar (q x)) ^ 2 =
      (ZMod.χ₄ (Fintype.card A : ZMod 4) : ℤ) * (Fintype.card A : ℂ) := by sorry
