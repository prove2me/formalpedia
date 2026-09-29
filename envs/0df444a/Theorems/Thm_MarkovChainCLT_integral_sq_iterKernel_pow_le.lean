-- Prove2me | Theorems.Thm_MarkovChainCLT_integral_sq_iterKernel_pow_le
-- name    : MarkovChainCLT.integral_sq_iterKernel_pow_le
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-16T00:14:03.520018+00:00
-- url     : https://prove2.me/theorems/0942c177-73eb-419b-99df-78d31b72076a
-- title:
--   Geometric $L^2$ decay of the transition operator on mean-zero functions
-- statement:
--   **Geometric decay of the transition operator on mean-zero $L^2$ functions.** If the $N$-step kernel is uniformly close to $\pi$ in total variation — precisely, $\sup_x\|P^N(x,\cdot)-\pi\| \le \rho$ with $4\rho \le 1/4$ — then for every square-integrable $h$ with $\mathbb E_\pi h = 0$ and every $j$,
--   $$\bigl\|P^{jN}h\bigr\|_{L^2(\pi)}^2 \;\le\; 4^{-j}\,\|h\|_{L^2(\pi)}^2 .$$
--
--   **What this gives.** Uniform ergodicity supplies such an $N$ (take $Rt^N$ small), so $\|P^n h\|_{L^2(\pi)} \le 2^{-\lfloor n/N\rfloor}\|h\|_{L^2(\pi)}$: the transition operator decays **geometrically** on the mean-zero subspace of $L^2(\pi)$, with a rate depending only on the chain. Two consequences drive the Markov chain central limit theorem for square-integrable observables:
--
--   * **Summable covariances.** Under the stationary chain, $\mathbb E[h(X_0)h(X_n)] = \int h\,(P^nh)\,d\pi$, so by Cauchy–Schwarz $|\mathbb E[h(X_0)h(X_n)]| \le \|h\|_2\|P^nh\|_2$, and $\sum_n \|P^nh\|_2 \le 2N\|h\|_2 < \infty$. Hence $\operatorname{Var}(\sum_{k<n}h(X_k)) = O(n\|h\|_2^2)$ with a constant depending only on $P$ — the estimate that controls the truncation error when passing from bounded to $L^2$ observables.
--   * **The Poisson equation in $L^2$.** The Neumann series $\sum_{n\ge0}P^nh$ converges in $L^2(\pi)$ and solves $\hat h - P\hat h = h$.
--
--   **Proof.** Induction on $j$, with the function generalized so that the induction hypothesis can be applied to $P^Nh$ rather than to $h$. Three ingredients recur:
--
--   1. *Invariance for all powers*: $P^n\circ\pi = \pi$, by induction from $P\circ\pi=\pi$.
--   2. *Jensen*: $(P^m u)^2 \le P^m(u^2)$ pointwise almost everywhere, from the nonnegativity of $\int (u - P^mu(x))^2\,dP^m(x,\cdot)$. This gives both integrability of $(P^mu)^2$ and, with invariance, that $P^mu$ still has $\pi$-mean zero — so the hypotheses of the contraction estimate are preserved along the induction.
--   3. *Semigroup*: $P^{(j+1)N} = P^N\circ P^{jN}$, so $P^{(j+1)N}u = P^{jN}(P^Nu)$ almost everywhere (Fubini for a composed kernel, applied at those $x$ where $u$ is integrable — a full-measure set by invariance).
--
--   Then $\|P^{(j+1)N}u\|_2^2 = \|P^{jN}(P^Nu)\|_2^2 \le 4^{-j}\|P^Nu\|_2^2 \le 4^{-j}\cdot\tfrac14\|u\|_2^2$, the last step being one application of the contraction estimate.
-- source:
--   S. P. Meyn and R. L. Tweedie, Markov Chains and Stochastic Stability, 2nd ed., Cambridge 2009, Ch. 16; E. Nummelin, General Irreducible Markov Chains and Non-negative Operators, Cambridge 1984, Ch. 6; L. Tierney, "Markov Chains for Exploring Posterior Distributions", Annals of Statistics 22 (1994) 1701-1728; G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320.

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovIterKernel
import Definitions.Def_TotalVariationDist
import Mathlib.Probability.Kernel.Invariance
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter Function MeasurableSpace MeasureTheory ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

theorem MarkovChainCLT.integral_sq_iterKernel_pow_le {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π) (N : ℕ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : 4 * ρ ≤ 1 / 4)
    (hrate : ∀ x, tvDist (iterKernel P N x) π ≤ ρ)
    (h : X → ℝ) (hh : Measurable h) (hL2 : Integrable (fun x => (h x) ^ 2) π)
    (hmean : ∫ x, h x ∂π = 0) (j : ℕ) :
    ∫ x, (∫ y, h y ∂(iterKernel P (j * N) x)) ^ 2 ∂π
      ≤ (1 / 4 : ℝ) ^ j * ∫ x, (h x) ^ 2 ∂π := by sorry
