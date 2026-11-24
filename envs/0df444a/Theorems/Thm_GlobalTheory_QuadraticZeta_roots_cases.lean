-- Prove2me | Theorems.Thm_GlobalTheory_QuadraticZeta_roots_cases
-- name    : GlobalTheory.QuadraticZeta.roots_cases
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:12:55.840801+00:00
-- url     : https://prove2.me/theorems/bdea46de-1fb2-4e33-a27d-0e2652982a0f
-- title:
--   Quadratic Zeta: roots cases
-- statement:
--   The Quadratic Zeta construction uses the roots cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L101-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L101-L133

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

theorem GlobalTheory.QuadraticZeta.roots_cases (t n : ℤ) {p : ℕ} (hp : p.Prime) :
    (kroneckerAt (t ^ 2 - 4 * n) p = -1 ∧ ∀ β : ZMod p, β ^ 2 ≠ t * β - n) ∨
    ∃ β β' : ZMod p, β + β' = t ∧ β * β' = n ∧
      ((kroneckerAt (t ^ 2 - 4 * n) p = 0 ∧ β = β') ∨
        (kroneckerAt (t ^ 2 - 4 * n) p = 1 ∧ β ≠ β')) := by sorry
