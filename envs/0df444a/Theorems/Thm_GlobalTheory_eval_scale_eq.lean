-- Prove2me | Theorems.Thm_GlobalTheory_eval_scale_eq
-- name    : GlobalTheory.eval_scale_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:19:43.971925+00:00
-- url     : https://prove2.me/theorems/a31b3e88-07e0-46f2-ad5a-2bb7919013bc
-- title:
--   Global Theory: eval scale eq
-- statement:
--   The Global Theory construction uses the eval scale eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ColumnDegreeLe.lean#L54-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ColumnDegreeLe.lean#L54-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ColumnDegreeLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory

theorem GlobalTheory.eval_scale_eq {K σ : Type*} [Field K] (w : σ → ℕ) (P : MvPolynomial σ K) (x : σ → K)
    (t : K) :
    eval (fun s => t ^ w s * x s) P =
      (∑ m ∈ P.support, Polynomial.monomial (∑ s ∈ m.support, w s * m s)
        (coeff m P * ∏ s ∈ m.support, x s ^ m s)).eval t := by sorry
