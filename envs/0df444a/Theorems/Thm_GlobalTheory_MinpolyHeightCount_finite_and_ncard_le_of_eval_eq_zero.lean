-- Prove2me | Theorems.Thm_GlobalTheory_MinpolyHeightCount_finite_and_ncard_le_of_eval_eq_zero
-- name    : GlobalTheory.MinpolyHeightCount.finite_and_ncard_le_of_eval_eq_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:24:39.096792+00:00
-- url     : https://prove2.me/theorems/ba1b3972-d312-44e4-9ce0-d4a153d24d37
-- title:
--   Minpoly Height Count: finite and ncard le of eval eq zero
-- statement:
--   The Minpoly Height Count construction uses the finite and ncard le of eval eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FiniteAndNcardMinpolyCoeffHeightLe.lean#L25-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FiniteAndNcardMinpolyCoeffHeightLe.lean#L25-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FiniteAndNcardMinpolyCoeffHeightLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open GlobalTheory GlobalTheory.MinpolyHeightCount

theorem GlobalTheory.MinpolyHeightCount.finite_and_ncard_le_of_eval_eq_zero {L : Type*} [Field L] {S : Set L} {p : L[X]}
    (hp : p ≠ 0) (hS : ∀ x ∈ S, p.eval x = 0) : S.Finite ∧ S.ncard ≤ p.natDegree := by sorry
