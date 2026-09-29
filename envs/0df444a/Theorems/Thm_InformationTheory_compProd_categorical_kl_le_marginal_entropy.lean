-- Prove2me | Theorems.Thm_InformationTheory_compProd_categorical_kl_le_marginal_entropy
-- name    : InformationTheory.compProd_categorical_kl_le_marginal_entropy
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-02T00:19:15.449932+00:00
-- url     : https://prove2.me/theorems/c08c2dab-0bf2-4ac0-afc8-8a2adee43840
-- title:
--   Conditional finite-valued KL divergence is bounded by marginal entropy
-- statement:
--   Let $\mu$ be a probability measure on a standard Borel space $\mathcal X$, let $\kappa$ be a Markov kernel from $\mathcal X$ to a finite action set $[k]$, and put $p=\mu\kappa$. The joint law $\mu\otimes\kappa$ and the independent coupling $\mu\otimes p$ satisfy
--
--   $$
--   D\!\left(\mu\otimes\kappa\,\middle\|\,\mu\otimes p\right)
--   \;\le\;
--   H(p)
--   =\sum_{a\in[k]}-p(a)\log p(a).
--   $$
--
--   This is the conditional-kernel form of the standard fact that mutual information with a finite-valued random variable is bounded by that variable’s entropy. It is designed for reuse when a joint law is represented by a regular conditional distribution.
--
--   **Formalization Note** The second measure is expressed as a composition-product with a constant kernel, and KL divergence is converted from extended nonnegative reals only after finiteness is established.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), printed pp. 470–471, Theorem 36.6 and Lemma 36.7, https://tor-lattimore.com/downloads/book/book.pdf; conditional-kernel form of the entropy step.

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal BigOperators ProbabilityTheory

namespace InformationTheory

theorem compProd_categorical_kl_le_marginal_entropy
    {Alpha : Type} {mAlpha : MeasurableSpace Alpha}
    [StandardBorelSpace Alpha] [Nonempty Alpha]
    {k : ℕ} [NeZero k] (mu : Measure Alpha) [IsProbabilityMeasure mu]
    (kappa : Kernel Alpha (Fin k)) [IsMarkovKernel kappa] :
    (klDiv (mu ⊗ₘ kappa)
      (mu ⊗ₘ Kernel.const Alpha (kappa ∘ₘ mu))).toReal ≤
      ∑ a, Real.negMulLog ((kappa ∘ₘ mu).real {a}) := by
  sorry

end InformationTheory
