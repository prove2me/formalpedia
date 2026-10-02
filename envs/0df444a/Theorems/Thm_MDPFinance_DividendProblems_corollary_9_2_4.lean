-- Prove2me | Theorems.Thm_MDPFinance_DividendProblems_corollary_9_2_4
-- name    : MDPFinance.DividendProblems.corollary_9_2_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:13:14.322304+00:00
-- url     : https://prove2.me/theorems/9682bf36-795b-4e5d-8452-4beaf59720d0
-- title:
--   Corollary 9.2.4 — the two degenerate cases
-- statement:
--   Two sign-definite special cases of Theorem 9.2.3 a), each with an easy economic explanation given in the book's own text: if the reserve's increments are never positive, paying out everything immediately and stopping is optimal ($J_\infty(x)=x^+$); if they are never negative, ruin is impossible but discounting still makes paying out as fast as possible optimal ($J_\infty(x)=x+\beta\mathbb EZ/(1-\beta)$).
--
--   **Moderation note.** Part b) was vacuous in the draft because the model carried `ℙ(Z < 0) > 0` as a field; with that assumption moved out of the structure it is now a genuine statement. Both parts state `f^*(x) = x⁺` for all `x`, as the book does; probabilities are compared in `[0,∞]` rather than through `toReal`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 275, PDF 285, Corollary 9.2.4

import Mathlib
import Definitions.Def_MDPFinance_DividendProblems_MDM
import Definitions.Def_MDPFinance_DividendProblems_Dividend

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory

namespace MDPFinance.DividendProblems

/-- Corollary 9.2.4 (Bäuerle–Rieder, p. 275, PDF 285). a) If `\mathbb P(Z \le 0) = 1` then
`J_\infty(x) = x^+` and `f^*(x) = x^+`. b) If `\mathbb P(Z \ge 0) = 1` then `J_\infty(x) = x +
\beta\mathbb EZ/(1-\beta)` for `x \ge 0` and `f^*(x) = x^+`. -/
theorem corollary_9_2_4 (M : DividendModel) (fstar : ℤ → ℕ) (hfstar : M.IsLargestMaximizer fstar) :
    (M.Zpmf.toMeasure {k : ℤ | k ≤ 0} = 1 →
        (∀ x : ℤ, M.Jinf x = ((max x 0).toNat : ℝ≥0∞)) ∧ ∀ x : ℤ, (fstar x : ℤ) = max x 0) ∧
      (M.Zpmf.toMeasure {k : ℤ | 0 ≤ k} = 1 →
        (∀ x : ℤ, 0 ≤ x → M.Jinf x = ENNReal.ofReal ((x : ℝ) + M.β * M.EZ / (1 - M.β))) ∧
          ∀ x : ℤ, (fstar x : ℤ) = max x 0) := by sorry

end MDPFinance.DividendProblems
