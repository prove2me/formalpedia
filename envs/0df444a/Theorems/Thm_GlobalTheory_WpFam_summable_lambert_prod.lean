-- Prove2me | Theorems.Thm_GlobalTheory_WpFam_summable_lambert_prod
-- name    : GlobalTheory.WpFam.summable_lambert_prod
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:57:14.077985+00:00
-- url     : https://prove2.me/theorems/9472117e-706d-4dcb-8e69-789496e3ec0b
-- title:
--   Wp Fam: summable lambert prod
-- statement:
--   The Wp Fam construction uses the summable lambert prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumLambertDoubleSeriesDivisors.lean#L9-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumLambertDoubleSeriesDivisors.lean#L9-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumLambertDoubleSeriesDivisors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
open GlobalTheory GlobalTheory.WpFam

theorem GlobalTheory.WpFam.summable_lambert_prod (e : ℕ) (Q : ℂ) (c : ℕ → ℕ → ℂ) (hQ : ‖Q‖ < 1)
    (hc : ∀ d m, ‖c d m‖ ≤ 1) :
    Summable fun x : ℕ+ × ℕ+ =>
      ((x.2 : ℕ) : ℂ) ^ e * c x.1 x.2 * Q ^ ((x.1 : ℕ) * (x.2 : ℕ)) := by sorry
