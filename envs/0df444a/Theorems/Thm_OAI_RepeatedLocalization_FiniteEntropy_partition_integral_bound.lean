-- Prove2me | Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_partition_integral_bound
-- name    : OAI.RepeatedLocalization.FiniteEntropy.partition_integral_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T19:52:54.005168+00:00
-- url     : https://prove2.me/theorems/6529bf21-8ce7-4244-b2f2-bd832877eb3d
-- title:
--   Fiberwise integral comparison over a countable measurable partition
-- statement:
--   Let $(\alpha,\mathcal A)$ be a measurable space with a measure $\mu$ (not assumed to be finite), let $\iota$ be a countable set equipped with a $\sigma$-algebra in which every singleton is measurable, and let $L:\alpha\to\iota$ be measurable, so that the fibers $L^{-1}(i)$ form a countable measurable partition of $\alpha$. Let $f,g:\alpha\to\mathbb R$ be such that $f(x)\ge0$ for every $x\in\alpha$, $f$ is integrable on each fiber $L^{-1}(i)$, and $g$ is $\mu$-integrable on $\alpha$. If
--
--   $$
--   \int_{L^{-1}(i)}f\,d\mu\;\le\;\int_{L^{-1}(i)}g\,d\mu\qquad\text{for every }i\in\iota ,
--   $$
--
--   then:
--
--   1. $f$ is $\mu$-integrable on all of $\alpha$, and
--   2. $\displaystyle\int_\alpha f\,d\mu\le\int_\alpha g\,d\mu$.
--
--   The result lets one check both global integrability and an integral comparison one fiber at a time, without knowing in advance that $f$ is integrable. In the localization argument the partition is by the history of a truncated run, and the lemma turns a computation of the expected one-step reward on each history into a bound on its overall expectation.
--
--   **Formalization Note** Integrability on a fiber is `IntegrableOn f {x | L x = i} μ`, and the integrals are Bochner integrals.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Localization/CountableIntegrals.lean#L79-L96

import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Definitions.Def_OAI_Probability_Localization_History
import Definitions.Def_OAI_Probability_Localization_Rewards

open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem OAI.RepeatedLocalization.FiniteEntropy.partition_integral_bound {α ι : Type*} [MeasurableSpace α] [MeasurableSpace ι]
    [Countable ι] [MeasurableSingletonClass ι] (μ : Measure α)
    (L : α → ι) (hL : Measurable L) {f g : α → ℝ} (hf0 : ∀ x,0 ≤ f x)
    (hf : ∀ i,IntegrableOn f {x | L x = i} μ) (hg : Integrable g μ)
    (hb : ∀ i,(∫ x in {x | L x = i},f x ∂μ) ≤ ∫ x in {x | L x = i},g x ∂μ) :
    Integrable f μ ∧ (∫ x,f x ∂μ) ≤ ∫ x,g x ∂μ := by sorry
