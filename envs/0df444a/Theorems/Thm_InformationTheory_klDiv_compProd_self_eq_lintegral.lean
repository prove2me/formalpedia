-- Prove2me | Theorems.Thm_InformationTheory_klDiv_compProd_self_eq_lintegral
-- name    : InformationTheory.klDiv_compProd_self_eq_lintegral
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T16:43:56.380837+00:00
-- url     : https://prove2.me/theorems/2ba0d590-b149-4bc3-aed8-286911cba563
-- title:
--   Conditional relative entropy as an average of fibrewise divergences
-- statement:
--   The conditional relative entropy of two composition-products with a common first marginal is the average of the fibrewise divergences.
--
--   Let $\mu$ be a finite measure on $(\mathcal A,\mathcal F)$ and let $\kappa,\eta$ be finite kernels from $\mathcal A$ to $(\mathcal B,\mathcal G)$ with $\kappa_a\ll\eta_a$ for every $a$. Then
--
--   $$
--   D\big(\mu\otimes\kappa \,\big\Vert\, \mu\otimes\eta\big) \;=\; \int_{\mathcal A} D\big(\kappa_a\,\Vert\,\eta_a\big)\,\mathrm d\mu(a).
--   $$
--
--   In words: if two joint laws agree on the first coordinate and differ only in the conditional law of the second, the divergence between them is exactly the expected divergence between the conditionals.
--
--   This is the quantity usually written $D(\kappa\Vert\eta\mid\mu)$ and called the *conditional relative entropy*. The chain rule for relative entropy is normally stated with this term on the right — as in Lattimore and Szepesvari's Exercise 14.12, $D(P,Q)=\sum_t \mathbb E_P\big[D(P_t(\cdot\mid X_1,\dots,X_{t-1}),Q_t(\cdot\mid X_1,\dots,X_{t-1}))\big]$ — so this identity is what turns an abstract chain rule into a computation one round at a time.
--
--   **Formalization Note** Mathlib's chain rule `klDiv_compProd_eq_add` leaves the conditional term in the unevaluated form `klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)`. The countability hypothesis on the pair of spaces is what makes the fibrewise Radon-Nikodym derivative jointly measurable, and is satisfied in the standard-Borel settings where the chain rule is applied.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), https://tor-lattimore.com/downloads/book/book.pdf : Exercise 14.12 (Chain rule), printed p. 196, where the conditional term of the decomposition is written as an expectation of the divergences between the regular conditional distributions.

import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Kernel.RadonNikodym

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

theorem InformationTheory.klDiv_compProd_self_eq_lintegral {α β : Type*}
    {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ : Measure α) [IsFiniteMeasure μ] (κ η : Kernel α β)
    [IsFiniteKernel κ] [IsFiniteKernel η] (hac : ∀ a, κ a ≪ η a) :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ a, klDiv (κ a) (η a) ∂μ := by
  sorry
