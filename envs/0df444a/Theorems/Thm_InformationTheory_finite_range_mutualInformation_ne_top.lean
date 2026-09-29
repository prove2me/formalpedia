-- Prove2me | Theorems.Thm_InformationTheory_finite_range_mutualInformation_ne_top
-- name    : InformationTheory.finite_range_mutualInformation_ne_top
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-02T04:26:17.880806+00:00
-- url     : https://prove2.me/theorems/f2012c4d-b1c7-48ae-910c-121ca80f3319
-- title:
--   Mutual information with a finite-valued variable is finite
-- statement:
--   Let $\mu$ be a probability measure, let $F$ be a measurable random variable with arbitrary measurable codomain, and let $G$ be a measurable random variable taking values in the nonempty finite set $\{0,\ldots,k-1\}$. Then the mutual information between $F$ and $G$ is finite:
--
--   $$
--   D\!\left(\mathcal L_\mu(F,G)\,\middle\|\,\mathcal L_\mu(F)\otimes\mathcal L_\mu(G)\right)<\infty.
--   $$
--
--   This finiteness lemma permits conversion of the extended-real mutual information to a real number in finite-action information-ratio arguments.
--
--   **Formalization Note** The conclusion is expressed as non-equality to $\infty$ for Lean’s extended nonnegative real-valued Kullback–Leibler divergence.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (2020), Lemma 36.7, printed p. 470 / free PDF p. 479; standard bound I(F;G) <= H(G) <= log k.

import Theorems.Thm_InformationTheory_klDiv_compProd_self_eq_lintegral_of_ae
import Theorems.Thm_InformationTheory_klDiv_map_measurableEmbedding
import Theorems.Thm_InformationTheory_finite_range_mutualInformation_le_marginal_entropy
import Theorems.Thm_InformationTheory_categorical_toReal_klDiv_eq_sum
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal ProbabilityTheory

namespace InformationTheory

theorem finite_range_mutualInformation_ne_top
    {Omega Alpha : Type*} {mOmega : MeasurableSpace Omega}
    {mAlpha : MeasurableSpace Alpha} {k : ℕ} [NeZero k]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (f : Omega → Alpha) (g : Omega → Fin k)
    (hf : Measurable f) (hg : Measurable g) :
    klDiv (mu.map (fun x ↦ (f x, g x)))
      ((mu.map f).prod (mu.map g)) ≠ ∞ := by sorry
