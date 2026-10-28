-- Prove2me | Theorems.Thm_OAI_PiExponent_AnalyticCollision_translated_row_determinant_exp_bound_q68
-- name    : OAI.PiExponent.AnalyticCollision.translated_row_determinant_exp_bound_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:15:26.768104+00:00
-- url     : https://prove2.me/theorems/32190539-919c-4ef9-9d88-ed161386eba4
-- title:
--   OAI.PiExponent.AnalyticCollision.translated_row_determinant_exp_bound_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.AnalyticCollision.translated_row_determinant_exp_bound` of [lean/OAI/NumberTheory/PiExponent/Analysis/AnalyticDeterminantCollision.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Analysis/AnalyticDeterminantCollision.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent.AnalyticCollision`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem translated_row_determinant_exp_bound_q68
--       {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
--       (group : ι → κ) (f : κ → ι → ℂ → ℂ)
--       (center : ι → ℂ) (ell : ι → ℕ)
--       (R : NNReal) (hR : 0 < R) {H A v : ℝ} (hH : 0 < H)
--       (hf : ∀ a j, Differentiable ℂ (f a j))
--       (hfD : ∀ a j z, z ∈ Metric.sphere (0 : ℂ) (R : ℝ) →
--         ‖f a j z‖ ≤ Real.exp (H * A))
--       (hc : ∀ i, ‖center i‖ + 3 / 4 ≤ (R : ℝ) / 2)
--       (hell : ((∑ i, ell i : ℕ) : ℝ) ≤ (Fintype.card ι : ℝ) * H / v) :
--       ‖Matrix.det (fun i j => rowTest (ell i)
--           (fun t => f (group i) j (center i + Complex.log (1 + t))))‖ ≤
--         Real.exp (-(Real.log 2 / 4) *
--           (∑ a, (Collision.multiplicity Finset.univ group a : ℝ) ^ 2) +
--           (Fintype.card ι : ℝ) * H *
--             (A + Real.log 2 / v + Collision.collisionRemainder (Fintype.card ι) H))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponent.AnalyticCollision.rowTest`, `OAI.PiExponent.Collision.collisionRemainder` and `OAI.PiExponent.Collision.multiplicity` (definitions bundle `OAIQ068A006` of this split).
--
--   **Used by.** The proof of `OAI.PiExponent.LiteralAnalytic.norm_actual_summand_le_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Analysis/AnalyticDeterminantCollision.lean (declaration OAI.PiExponent.AnalyticCollision.translated_row_determinant_exp_bound)

import Mathlib
import Definitions.Def_OAIQ068A006

section

attribute [-instance] _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace PiExponent.AnalyticCollision

theorem translated_row_determinant_exp_bound_q68
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (f : κ → ι → ℂ → ℂ)
    (center : ι → ℂ) (ell : ι → ℕ)
    (R : NNReal) (hR : 0 < R) {H A v : ℝ} (hH : 0 < H)
    (hf : ∀ a j, Differentiable ℂ (f a j))
    (hfD : ∀ a j z, z ∈ Metric.sphere (0 : ℂ) (R : ℝ) →
      ‖f a j z‖ ≤ Real.exp (H * A))
    (hc : ∀ i, ‖center i‖ + 3 / 4 ≤ (R : ℝ) / 2)
    (hell : ((∑ i, ell i : ℕ) : ℝ) ≤ (Fintype.card ι : ℝ) * H / v) :
    ‖Matrix.det (fun i j => rowTest (ell i)
        (fun t => f (group i) j (center i + Complex.log (1 + t))))‖ ≤
      Real.exp (-(Real.log 2 / 4) *
        (∑ a, (Collision.multiplicity Finset.univ group a : ℝ) ^ 2) +
        (Fintype.card ι : ℝ) * H *
          (A + Real.log 2 / v + Collision.collisionRemainder (Fintype.card ι) H)) := by
  sorry

end PiExponent.AnalyticCollision

end OAI
end
