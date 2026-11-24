-- Prove2me | Theorems.Thm_MBRLGuarantees_value_gap_le_lipschitz_model_error
-- name    : MBRLGuarantees.value_gap_le_lipschitz_model_error
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T11:26:00.412656+00:00
-- url     : https://prove2.me/theorems/e8eb32a5-b971-4eb6-8e06-a2a002fa4e49
-- title:
--   Lemma 4.1: prediction error bounds the value discrepancy
-- statement:
--   Let the states be points of a normed space $E$ (an injective measurable map $\iota:\mathcal S\to E$, with $E$ second countable and carrying its Borel $\sigma$-algebra), let $\gamma\in[0,1)$, let $R$ be bounded and measurable, and let $S_0\sim\mu_0$. Let $M^\star$ and $\widehat M$ be deterministic measurable models and $\pi$ a policy. Suppose the imaginary value function is $L$-Lipschitz,
--
--   $$|V^{\pi,\widehat M}(s)-V^{\pi,\widehat M}(s')|\le L\,\|s-s'\|\qquad\text{for all }s,s'\in\mathcal S.$$
--
--   Then
--
--   $$\big|V^{\pi,\widehat M}-V^{\pi,M^\star}\big|\le\kappa L\,\mathbb E_{S\sim\rho^{\pi},\ A\sim\pi(\cdot\mid S)}\big[\|\widehat M(S,A)-M^\star(S,A)\|\big],$$
--
--   with $\rho^\pi=\rho^{\pi,M^\star}$ and $\kappa=\gamma(1-\gamma)^{-1}$.
--
--   **Formalization Note** The right side is a $[0,\infty]$-valued integral, so the bound is also stated when the expected prediction error is infinite.
-- source:
--   Luo, Xu, Li, Tian, Darrell and Ma, Algorithmic Framework for Model-based Deep Reinforcement Learning with Theoretical Guarantees, arXiv:1807.03858v5 (ICLR 2019), Section 4.1, Lemma 4.1, eqs. (4.1)-(4.2), p. 6; proof in Appendix C.3, p. 19

import Mathlib
import Definitions.Def_MBRLGuarantees_Basic

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace MBRLGuarantees

theorem value_gap_le_lipschitz_model_error {S A E : Type*} [MeasurableSpace S]
    [MeasurableSpace A] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (ι : S → E) (hι : Function.Injective ι) (hιm : Measurable ι)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (R : S × A → ℝ) (hRm : Measurable R) (hRb : ∃ C, ∀ x, |R x| ≤ C)
    (μ₀ : Measure S) [IsProbabilityMeasure μ₀] (pi : Kernel S A) [IsMarkovKernel pi]
    (mstar mhat : S × A → S) (hmstar : Measurable mstar) (hmhat : Measurable mhat) (L : ℝ)
    (hL : ∀ s s', |stateValue γ R pi (Kernel.deterministic mhat hmhat) s -
      stateValue γ R pi (Kernel.deterministic mhat hmhat) s'| ≤ L * ‖ι s - ι s'‖) :
    ENNReal.ofReal |value γ R μ₀ pi (Kernel.deterministic mhat hmhat) -
        value γ R μ₀ pi (Kernel.deterministic mstar hmstar)| ≤
      ENNReal.ofReal (kappa γ * L) *
        ∫⁻ s, ∫⁻ a, ENNReal.ofReal ‖ι (mhat (s, a)) - ι (mstar (s, a))‖ ∂(pi s)
          ∂(occ γ μ₀ pi (Kernel.deterministic mstar hmstar)) := by sorry

end MBRLGuarantees
