-- Prove2me | Theorems.Thm_OAI_RepeatedLocalization_log_sum_inequality
-- name    : OAI.RepeatedLocalization.log_sum_inequality
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:25:31.090054+00:00
-- url     : https://prove2.me/theorems/26627867-a461-473f-bdf1-af920adf4033
-- title:
--   Log-sum inequality: (∑ a) log(∑ a) ≤ ∑ a_i log(a_i / b_i) for a ≥ 0 and a probability vector b
-- statement:
--   Let $\iota$ be a finite type, and let $a, b : \iota \to \mathbb{R}$ satisfy:
--   - $a_i \ge 0$ and $b_i \ge 0$ for all $i$ (`ha`, `hb`);
--   - $\sum_i b_i = 1$ (`hb1`);
--   - $a_i = 0$ whenever $b_i = 0$ (`hz`).
--
--   Then
--   $$\Bigl(\sum_i a_i\Bigr)\log\Bigl(\sum_i a_i\Bigr) \;\le\; \sum_i a_i \log\frac{a_i}{b_i}.$$
--   Lean's conventions $\log 0 = 0$ and $x/0 = 0$ apply, so terms with $a_i = 0$ contribute $0$.
--
--   This is the log-sum inequality $\sum_i a_i\log(a_i/b_i) \ge \bigl(\sum_i a_i\bigr)\log\bigl(\sum_i a_i/\sum_i b_i\bigr)$, in the case $\sum_i b_i = 1$.
--
--   Lean: `OAI.RepeatedLocalization.log_sum_inequality`. This is OpenAI's lemma `finite_log_sum` in `lean/OAI/Probability/GaussianInformation/Dyadic/Entropy.lean`, with OpenAI's definition `xlog x = x * Real.log x` written out, so that the statement uses only Mathlib.
-- source:
--   The log-sum inequality (see T. M. Cover and J. A. Thomas, Elements of Information Theory, 2nd ed., Wiley, 2006, Theorem 2.7.1). Lean proof: OpenAI, Localization costs and information growth for exact Gaussian observations, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 140; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Localization-costs-and-information-growth-for-exact-Gaussian-observations-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GaussianInformation/Dyadic/Entropy.lean (declaration OAI.RepeatedLocalization.finite_log_sum, stated here with its definition xlog written out)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization

lemma log_sum_inequality {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hb1 : ∑ i, b i = 1)
    (hz : ∀ i, b i = 0 → a i = 0) :
    (∑ i, a i) * Real.log (∑ i, a i) ≤ ∑ i, a i * Real.log (a i / b i) := by
  sorry

end RepeatedLocalization

end OAI
end
