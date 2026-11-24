-- Prove2me | Theorems.Thm_MBRLGuarantees_meta_algorithm_monotone
-- name    : MBRLGuarantees.meta_algorithm_monotone
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T11:51:18.832263+00:00
-- url     : https://prove2.me/theorems/fe9f453f-b23f-4de7-8746-e7ec03759310
-- title:
--   Theorem 3.1: the meta-algorithm improves the true value monotonically
-- statement:
--   Let $\gamma\in[0,1)$, let $R$ be bounded and measurable, and let $S_0\sim\mu_0$. Let $\Pi$ be a family of policies and $\mathcal M$ a family of models (Markov kernels) with $M^\star\in\mathcal M$. Let $D_{\pi_{\mathrm{ref}}}(M,\pi)\ge0$ be a discrepancy bound and $d$ a policy distance with values in $[0,\infty]$, let $\delta\in[0,\infty]$, and assume
--
--   - (R1) $V^{\pi,M^\star}\ge V^{\pi,\widehat M}-D_{\pi_{\mathrm{ref}}}(\widehat M,\pi)$ for all policies $\pi,\pi_{\mathrm{ref}}$ and models $\widehat M$ with $d(\pi,\pi_{\mathrm{ref}})\le\delta$;
--   - (R2) $D_{\pi_{\mathrm{ref}}}(M^\star,\pi)=0$ for all policies $\pi,\pi_{\mathrm{ref}}$;
--   - $d(\pi,\pi)=0$ for every $\pi\in\Pi$.
--
--   Run Algorithm 1 for $T$ iterations from $\pi_0\in\Pi$: for each $k<T$, $(\pi_{k+1},M_{k+1})\in\Pi\times\mathcal M$ satisfies $d(\pi_{k+1},\pi_k)\le\delta$ and maximises $V^{\pi,M}-D_{\pi_k}(M,\pi)$ over all $(\pi,M)\in\Pi\times\mathcal M$ with $d(\pi,\pi_k)\le\delta$. Then
--
--   $$V^{\pi_0,M^\star}\le V^{\pi_1,M^\star}\le\cdots\le V^{\pi_T,M^\star}.$$
--
--   This is the paper's guarantee of monotone improvement for model-based RL with an optimistic, jointly optimised lower bound.
--
--   **Formalization Note** The theorem's second claim, convergence to a local maximum, is not included. The hypotheses $\pi_0\in\Pi$ and $d(\pi,\pi)=0$ are not written in the paper, but its proof uses them when it takes $(\pi_k,M^\star)$ as a feasible point of iteration $k$. Without them the conclusion fails (see the mission report). "The optimisation problem is solvable at each iteration" is expressed by the maximisation property of the iterates.
-- source:
--   Luo, Xu, Li, Tian, Darrell and Ma, Algorithmic Framework for Model-based Deep Reinforcement Learning with Theoretical Guarantees, arXiv:1807.03858v5 (ICLR 2019), Section 3, Algorithm 1, eqs. (3.3)-(3.5), (R1), (R2), Theorem 3.1 (first claim), p. 5

import Mathlib
import Definitions.Def_MBRLGuarantees_Basic

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace MBRLGuarantees

theorem meta_algorithm_monotone {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (R : S × A → ℝ) (hRm : Measurable R) (hRb : ∃ C, ∀ x, |R x| ≤ C)
    (μ₀ : Measure S) [IsProbabilityMeasure μ₀]
    (Pol : Set (Kernel S A)) (hPol : ∀ pi ∈ Pol, IsMarkovKernel pi)
    (Mod : Set (Kernel (S × A) S)) (hMod : ∀ M ∈ Mod, IsMarkovKernel M)
    (Mstar : Kernel (S × A) S) (hMstar : Mstar ∈ Mod)
    (D : Kernel S A → Kernel (S × A) S → Kernel S A → ℝ) (hD0 : ∀ piref M pi, 0 ≤ D piref M pi)
    (d : Kernel S A → Kernel S A → ℝ≥0∞) (δ : ℝ≥0∞)
    (hR1 : ∀ (piref pi : Kernel S A) (Mhat : Kernel (S × A) S), IsMarkovKernel piref →
      IsMarkovKernel pi → IsMarkovKernel Mhat → d pi piref ≤ δ →
      value γ R μ₀ pi Mhat - D piref Mhat pi ≤ value γ R μ₀ pi Mstar)
    (hR2 : ∀ piref pi : Kernel S A, IsMarkovKernel piref → IsMarkovKernel pi →
      D piref Mstar pi = 0)
    (hdself : ∀ pi ∈ Pol, d pi pi = 0)
    (T : ℕ) (pol : ℕ → Kernel S A) (mod : ℕ → Kernel (S × A) S) (hpol0 : pol 0 ∈ Pol)
    (hstep : ∀ k < T, pol (k + 1) ∈ Pol ∧ mod (k + 1) ∈ Mod ∧ d (pol (k + 1)) (pol k) ≤ δ ∧
      ∀ pi ∈ Pol, ∀ M ∈ Mod, d pi (pol k) ≤ δ →
        value γ R μ₀ pi M - D (pol k) M pi ≤
          value γ R μ₀ (pol (k + 1)) (mod (k + 1)) - D (pol k) (mod (k + 1)) (pol (k + 1))) :
    ∀ i j, i ≤ j → j ≤ T → value γ R μ₀ (pol i) Mstar ≤ value γ R μ₀ (pol j) Mstar := by sorry

end MBRLGuarantees
