-- Prove2me | Theorems.Thm_MBRLGuarantees_norm_discrepancy_bound_near_reference
-- name    : MBRLGuarantees.norm_discrepancy_bound_near_reference
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T11:26:56.720848+00:00
-- url     : https://prove2.me/theorems/b6588269-3b74-4265-ad6c-c0d7800c2019
-- title:
--   Proposition 4.2 (as proved): prediction error under the reference policy's state distribution
-- statement:
--   In the setting of Lemma 4.1, let $\pi_{\mathrm{ref}}$ be a reference policy with $d^{\mathrm{KL}}(\pi,\pi_{\mathrm{ref}})\le\delta$, where $\delta\ge0$ and $s\mapsto\mathrm{KL}(\pi(\cdot\mid s),\pi_{\mathrm{ref}}(\cdot\mid s))$ is measurable, and suppose the states are uniformly bounded, $\|s\|\le B$ for all $s\in\mathcal S$. Then
--
--   $$\big|V^{\pi,\widehat M}-V^{\pi,M^\star}\big|\le\kappa L\,\mathbb E_{S\sim\rho^{\pi_{\mathrm{ref}}},\ A\sim\pi(\cdot\mid S)}\big[\|\widehat M(S,A)-M^\star(S,A)\|\big]+2\kappa^2L\delta B.$$
--
--   The first term only needs states sampled from the reference policy, which is what makes it estimable.
--
--   **Formalization Note** The paper prints the second term as $2\kappa^2\delta B$, without the factor $L$. That version is false: multiplying the reward by $c$ multiplies the left side and $L$ by $c$ and leaves $2\kappa^2\delta B$ unchanged (a two-state counterexample is in the mission report). The proof in Appendix C.3 multiplies the bound $\|\rho^\pi-\rho^{\pi_{\mathrm{ref}}}\|_1\cdot2B$ by $\kappa L$ and uses Corollary E.7 without its factor $\sqrt2$; with Corollary E.7 corrected, the paper's chain gives only $2\sqrt2\kappa^2L\delta B$. The constant $2\kappa^2L\delta B$ stated here is nevertheless true by a sharper step: the integrand $g(s)=\mathbb E_A\|\widehat M-M^\star\|$ lies in $[0,2B]$, so $\langle\rho^\pi-\rho^{\pi_{\mathrm{ref}}},g\rangle=\langle\rho^\pi-\rho^{\pi_{\mathrm{ref}}},g-B\rangle\le B\,|\rho^\pi-\rho^{\pi_{\mathrm{ref}}}|_1\le\sqrt2\kappa\delta B$. The right side is $[0,\infty]$-valued.
-- source:
--   Luo, Xu, Li, Tian, Darrell and Ma, Algorithmic Framework for Model-based Deep Reinforcement Learning with Theoretical Guarantees, arXiv:1807.03858v5 (ICLR 2019), Section 4.1, Proposition 4.2, eqs. (4.3)-(4.4), p. 6; proof in Appendix C.3, eqs. (C.2)-(C.3), p. 19

import Mathlib
import Definitions.Def_MBRLGuarantees_Basic

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace MBRLGuarantees

theorem norm_discrepancy_bound_near_reference {S A E : Type*} [MeasurableSpace S]
    [MeasurableSpace A] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (ι : S → E) (hι : Function.Injective ι) (hιm : Measurable ι)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (R : S × A → ℝ) (hRm : Measurable R) (hRb : ∃ C, ∀ x, |R x| ≤ C)
    (μ₀ : Measure S) [IsProbabilityMeasure μ₀] (pi piref : Kernel S A) [IsMarkovKernel pi]
    [IsMarkovKernel piref]
    (mstar mhat : S × A → S) (hmstar : Measurable mstar) (hmhat : Measurable mhat) (L : ℝ)
    (hL : ∀ s s', |stateValue γ R pi (Kernel.deterministic mhat hmhat) s -
      stateValue γ R pi (Kernel.deterministic mhat hmhat) s'| ≤ L * ‖ι s - ι s'‖)
    (δ : ℝ) (hδ : 0 ≤ δ) (hKL : Measurable fun s => klDiv (pi s) (piref s))
    (hd : dKL γ μ₀ (Kernel.deterministic mstar hmstar) pi piref ≤ ENNReal.ofReal δ)
    (B : ℝ) (hB : ∀ s, ‖ι s‖ ≤ B) :
    ENNReal.ofReal |value γ R μ₀ pi (Kernel.deterministic mhat hmhat) -
        value γ R μ₀ pi (Kernel.deterministic mstar hmstar)| ≤
      ENNReal.ofReal (kappa γ * L) *
          ∫⁻ s, ∫⁻ a, ENNReal.ofReal ‖ι (mhat (s, a)) - ι (mstar (s, a))‖ ∂(pi s)
            ∂(occ γ μ₀ piref (Kernel.deterministic mstar hmstar)) +
        ENNReal.ofReal (2 * kappa γ ^ 2 * L * δ * B) := by sorry

end MBRLGuarantees
