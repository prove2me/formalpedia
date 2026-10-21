-- Prove2me | Theorems.Thm_LipBernoulli_MultiUtility_proposition_2_1
-- name    : LipBernoulli.MultiUtility.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:13.754316+00:00
-- url     : https://prove2.me/theorems/2a15a8d6-33c2-4ea7-94d7-a3eb98061b19
-- title:
--   Proposition 2.1, p. 4 — finite mean of μ × μ ⇔ finite first moment ⇔ every Lipschitz function is integrable
-- statement:
--   Let $X = (X,d)$ be a nonempty metric space with its Borel $\sigma$-algebra and let $\mu$ be a finite positive Borel measure on $X$. The following are equivalent:
--
--   1. $\displaystyle\int_{X\times X} d\,\mathrm d(\mu\times\mu) < \infty$;
--   2. $\displaystyle\int_X d(\cdot, e)\,\mathrm d\mu < \infty$ for some $e \in X$;
--   3. $\displaystyle\int_X d(\cdot, e)\,\mathrm d\mu < \infty$ for every $e \in X$;
--   4. every Lipschitz function on $X$ is integrable against $\mu$.
--
--   In particular, $\Delta_1(X)$ is exactly the set of Borel probability measures with a finite first moment, and every Lipschitz function has a finite expectation under every $p \in \Delta_1(X)$, which is what makes the expected-utility integrals of the paper meaningful.
--
--   **Formalization Note** The paper's "(b) for some (any) $e$" is split into the two conditions 2 and 3, and the four conditions are stated as a list of pairwise equivalent propositions (`List.TFAE`). Nonemptiness of $X$ is added: for empty $X$, condition 2 fails while condition 1 holds trivially; a metric space is nonempty by the field's standing convention. The integrals of $d$ are lower Lebesgue integrals valued in $[0,\infty]$.
-- source:
--   Ok & Weaver, Lipschitz Bernoulli Utility Functions, arXiv:2104.11205v1, Proposition 2.1, p. 4

import Mathlib
import Definitions.Def_LipBernoulli_MultiUtility_Setting

open MeasureTheory
open scoped ENNReal NNReal

namespace LipBernoulli.MultiUtility

/-- Proposition 2.1, p. 4. For a finite positive Borel measure `μ` on a (nonempty) metric space `X`
the following are equivalent: (a) `∫ d d(μ × μ) < ∞`; (b) `∫ d(·, e) dμ < ∞` for some `e ∈ X`;
(b') the same for every `e ∈ X`; (c) every Lipschitz function on `X` is integrable against `μ`. -/
theorem proposition_2_1 {X : Type*} [MetricSpace X] [Nonempty X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] :
    List.TFAE
      [∫⁻ z, edist z.1 z.2 ∂(μ.prod μ) < ∞,
       ∃ e : X, ∫⁻ x, edist x e ∂μ < ∞,
       ∀ e : X, ∫⁻ x, edist x e ∂μ < ∞,
       ∀ f : X → ℝ, (∃ L : ℝ≥0, LipschitzWith L f) → Integrable f μ] := by sorry

end LipBernoulli.MultiUtility
