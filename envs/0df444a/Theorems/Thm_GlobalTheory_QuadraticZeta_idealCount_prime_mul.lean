-- Prove2me | Theorems.Thm_GlobalTheory_QuadraticZeta_idealCount_prime_mul
-- name    : GlobalTheory.QuadraticZeta.idealCount_prime_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:12:34.39242+00:00
-- url     : https://prove2.me/theorems/4ec4c98c-2f4e-4870-8d8f-60d05e58d0c0
-- title:
--   Quadratic Zeta: ideal Count prime mul
-- statement:
--   The Quadratic Zeta construction uses the ideal Count prime mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L239-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L239-L314

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped NumberTheorySymbols
open GlobalTheory GlobalTheory.QuadraticZeta
variable {K : Type*} [Field K] [NumberField K]

theorem GlobalTheory.QuadraticZeta.idealCount_prime_mul (h2 : finrank ℚ K = 2) {p : ℕ} (hp : p.Prime) (m : ℕ) :
    (idealCount K (p * m) : ℤ) = (1 + kroneckerAt (discr K) p) * idealCount K m
      - kroneckerAt (discr K) p * if p ∣ m then (idealCount K (m / p) : ℤ) else 0 := by sorry
