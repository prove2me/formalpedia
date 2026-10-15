-- Prove2me | Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_countable_cost_bound
-- name    : OAI.RepeatedLocalization.FiniteEntropy.countable_cost_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T19:52:23.22418+00:00
-- url     : https://prove2.me/theorems/cbf7eca7-de5c-490b-8ed0-342632522220
-- title:
--   Fiberwise cost bounds over a countable labelling integrate to a global bound
-- statement:
--   Let $(\alpha,\mathcal A)$ be a measurable space carrying a finite measure $\mu$, let $\iota$ be a countable set equipped with a $\sigma$-algebra in which every singleton is measurable, and let $L:\alpha\to\iota$ be measurable, so that the fibers $L^{-1}(i)$, $i\in\iota$, form a countable measurable partition of $\alpha$. Let $F:\iota\to\mathbb R$ be a cost with $F(i)\ge0$ for every $i$, and let $g:\alpha\to\mathbb R$ be $\mu$-integrable. Suppose that on every fiber the total cost is dominated by the integral of $g$:
--
--   $$
--   \mu\big(L^{-1}(i)\big)\,F(i)\;\le\;\int_{L^{-1}(i)}g\,d\mu\qquad\text{for every }i\in\iota .
--   $$
--
--   Then:
--
--   1. the function $x\mapsto F(L(x))$ is $\mu$-integrable, and
--   2. $\displaystyle\int_\alpha F(L(x))\,d\mu(x)\le\int_\alpha g\,d\mu$.
--
--   This is a local-to-global principle for costs that depend on a point only through a countable label: a budget verified separately on each fiber yields integrability and a bound for the expected cost. In the localization argument the label is the history of a truncated run, $F$ is the entropy-plus-depth cost of a history, and $g$ is a log-likelihood ratio plus accumulated rewards.
--
--   **Formalization Note** The fiber masses are extended nonnegative reals converted to real numbers with `toReal` (they are finite because $\mu$ is a finite measure), and the integrals are Bochner integrals.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Localization/CountableIntegrals.lean#L50-L77

import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Definitions.Def_OAI_Probability_Localization_History
import Definitions.Def_OAI_Probability_Localization_Rewards

open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem OAI.RepeatedLocalization.FiniteEntropy.countable_cost_bound {α ι : Type*} [MeasurableSpace α] [MeasurableSpace ι]
    [Countable ι] [MeasurableSingletonClass ι] (μ : Measure α) [IsFiniteMeasure μ]
    (L : α → ι) (hL : Measurable L) (F : ι → ℝ) (hF : ∀ i,0 ≤ F i)
    {g : α → ℝ} (hg : Integrable g μ)
    (hb : ∀ i,(μ {x | L x = i}).toReal * F i ≤ ∫ x in {x | L x = i},g x ∂μ) :
    Integrable (fun x => F (L x)) μ ∧ (∫ x,F (L x) ∂μ) ≤ ∫ x,g x ∂μ := by sorry
