-- Prove2me | Theorems.Thm_GlobalTheory_FibLine_sub_mul_eval_hPoly
-- name    : GlobalTheory.FibLine.sub_mul_eval_hPoly
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:23:08.926833+00:00
-- url     : https://prove2.me/theorems/888ebc45-e137-4c1f-a5df-fa0a6f2919ab
-- title:
--   Fib Line: sub mul eval h Poly
-- statement:
--   The Fib Line construction uses the sub mul eval h Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralAffinePowEqHPoly.lean#L10-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralAffinePowEqHPoly.lean#L10-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HPolyAddTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralAffinePowEqHPoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MeasureTheory MvPolynomial GlobalTheory.FibLine
open GlobalTheory GlobalTheory.FibLine

theorem GlobalTheory.FibLine.sub_mul_eval_hPoly (a b : ℂ) (k : ℕ) :
    (a - b) * MvPolynomial.eval ![a + b, a * b] (hPoly k) = a ^ (k + 1) - b ^ (k + 1) := by sorry
