-- Prove2me | Theorems.Thm_MBRLGuarantees_telescoping_lemma
-- name    : MBRLGuarantees.telescoping_lemma
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T11:25:30.575185+00:00
-- url     : https://prove2.me/theorems/a29ba0b1-9686-4720-9e03-7cdc86fc8cff
-- title:
--   Lemma 4.3: Telescoping Lemma
-- statement:
--   Let $\gamma\in[0,1)$, let the reward $R$ be bounded and measurable, let $S_0\sim\mu_0$, and let $\kappa=\gamma(1-\gamma)^{-1}$. For every policy $\pi$ and every two dynamical models $M,\widehat M$ (Markov kernels),
--
--   $$V^{\pi,\widehat M}-V^{\pi,M}=\kappa\,\mathbb E_{S\sim\rho^{\pi,M},\ A\sim\pi(\cdot\mid S)}\big[G^{\pi,\widehat M}(S,A)\big],$$
--
--   where $G^{\pi,\widehat M}(s,a)=\mathbb E_{\hat s'\sim\widehat M(\cdot\mid s,a)}V^{\pi,\widehat M}(\hat s')-\mathbb E_{s'\sim M(\cdot\mid s,a)}V^{\pi,\widehat M}(s')$ and $\rho^{\pi,M}$ is the discounted state distribution of $\pi$ on $M$.
--
--   The lemma decomposes the value gap between two models into one-step discrepancies along the state distribution of the second model; every discrepancy bound of the paper is derived from it.
--
--   **Formalization Note** The model inside $G$ is the second model $M$ of the lemma (the paper's display of $G$ writes $M^\star$). The expectation over $(S,A)$ is the iterated integral over $S\sim\rho^{\pi,M}$ and $A\sim\pi(\cdot\mid S)$.
-- source:
--   Luo, Xu, Li, Tian, Darrell and Ma, Algorithmic Framework for Model-based Deep Reinforcement Learning with Theoretical Guarantees, arXiv:1807.03858v5 (ICLR 2019), Section 4.1, Lemma 4.3, eq. (4.6), p. 7; proof in Appendix B, pp. 16-17

import Mathlib
import Definitions.Def_MBRLGuarantees_Basic

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace MBRLGuarantees

theorem telescoping_lemma {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (R : S × A → ℝ) (hRm : Measurable R) (hRb : ∃ C, ∀ x, |R x| ≤ C)
    (μ₀ : Measure S) [IsProbabilityMeasure μ₀]
    (pi : Kernel S A) [IsMarkovKernel pi] (M Mhat : Kernel (S × A) S) [IsMarkovKernel M]
    [IsMarkovKernel Mhat] :
    value γ R μ₀ pi Mhat - value γ R μ₀ pi M =
      kappa γ * ∫ s, ∫ a, gapFn γ R pi Mhat M s a ∂(pi s) ∂(occ γ μ₀ pi M) := by sorry

end MBRLGuarantees
