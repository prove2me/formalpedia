-- Prove2me | Theorems.Thm_GlobalTheory_CotangentSquare_det_ne_zero_of_mul_eq
-- name    : GlobalTheory.CotangentSquare.det_ne_zero_of_mul_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:27:01.9801+00:00
-- url     : https://prove2.me/theorems/686964c6-f9cd-49f6-92ef-b57e7019a667
-- title:
--   Cotangent Square: det ne zero of mul eq
-- statement:
--   The Cotangent Square construction uses the det ne zero of mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CotangentMapInjectiveOfSquarePresentationAtPoint.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CotangentMapInjectiveOfSquarePresentationAtPoint.lean#L26-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CotangentMapInjectiveOfSquarePresentationAtPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.CotangentSquare
open MvPolynomial
variable {O B σ : Type} [CommRing O] [CommRing B]

theorem GlobalTheory.CotangentSquare.det_ne_zero_of_mul_eq [Fintype σ] [DecidableEq σ] [IsDomain O] {N J : Matrix σ σ O}
    {c : O} (hc : c ≠ 0) (h : N * J = c • (1 : Matrix σ σ O)) : J.det ≠ 0 := by sorry
