-- Prove2me | Theorems.Thm_MarkovChainCLT_integral_sq_iterKernel_geom_le
-- name    : MarkovChainCLT.integral_sq_iterKernel_geom_le
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-16T00:22:15.989886+00:00
-- url     : https://prove2.me/theorems/e4189c74-d795-406e-97d7-e7ddacbf9c33
-- title:
--   Geometric $L^2$ decay of the transition operator at every lag
-- statement:
--   **Geometric $L^2$ decay at every lag.** For a chain whose $N$-step kernel satisfies the uniform total-variation bound $\sup_x\|P^N(x,\cdot)-\pi\|\le\rho$ with $4\rho\le 1/4$, and any bounded measurable $r$ with $\mathbb E_\pi r = 0$,
--   $$\bigl\|P^d r\bigr\|_{L^2(\pi)}^2 \;\le\; 4^{-\lfloor d/N\rfloor}\,\|r\|_{L^2(\pi)}^2 \qquad\text{for every } d,$$
--   i.e. $\|P^dr\|_{L^2(\pi)} \le 2^{-\lfloor d/N\rfloor}\|r\|_{L^2(\pi)}$.
--
--   **Why every lag, not just multiples of $N$.** The contraction estimate only sees the block length $N$: iterating it gives decay along $d = 0, N, 2N,\dots$. Filling in the intermediate lags requires the complementary fact that the transition operator is a **weak** contraction of $L^2(\pi)$ at every step — a consequence of Jensen's inequality $(P^mu)^2 \le P^m(u^2)$ together with the invariance $\mathbb E_\pi[P^m(u^2)] = \mathbb E_\pi[u^2]$. Writing $d = qN + s$ with $0\le s<N$ and using the semigroup property $P^d = P^{qN}\circ P^{s}$, one has $P^dr = P^{s}\bigl(P^{qN}r\bigr)$, so
--   $$\|P^dr\|_2 \;\le\; \|P^{qN}r\|_2 \;\le\; 2^{-q}\|r\|_2 .$$
--
--   **What it is for.** Under the stationary chain the covariance at lag $d$ is $\mathbb E[r(X_0)r(X_d)] = \int r\,(P^dr)\,d\pi$, so this bound gives
--   $$\sum_{d\ge0}\bigl|\mathbb E[r(X_0)r(X_d)]\bigr| \;\le\; \|r\|_2\sum_{d\ge0}\|P^dr\|_2 \;\le\; 2N\,\|r\|_2^2 ,$$
--   because each block of $N$ consecutive lags contributes at most $N2^{-q}\|r\|_2^2$. Summing the double series then yields the variance bound $\operatorname{Var}\bigl(\sum_{k<n}r(X_k)\bigr) = O\bigl(n\|r\|_2^2\bigr)$ with a constant depending only on the chain — the estimate that controls the truncation error when the Markov chain central limit theorem is extended from bounded to square-integrable observables.
-- source:
--   S. P. Meyn and R. L. Tweedie, Markov Chains and Stochastic Stability, 2nd ed., Cambridge 2009, Ch. 16; E. Nummelin, General Irreducible Markov Chains and Non-negative Operators, Cambridge 1984, Ch. 6; I. A. Ibragimov and Yu. V. Linnik, Independent and Stationary Sequences of Random Variables, Wolters-Noordhoff 1971; G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320.

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovIterKernel
import Definitions.Def_TotalVariationDist
import Mathlib.Probability.Kernel.Invariance
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter Function MeasurableSpace MeasureTheory ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

theorem MarkovChainCLT.integral_sq_iterKernel_geom_le {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π) (N : ℕ) (hN : 1 ≤ N) (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : 4 * ρ ≤ 1 / 4) (hrate : ∀ x, tvDist (iterKernel P N x) π ≤ ρ)
    (r : X → ℝ) (hr : Measurable r) (Br : ℝ) (hBr : ∀ x, |r x| ≤ Br)
    (hmean : ∫ x, r x ∂π = 0) (d : ℕ) :
    ∫ x, (∫ y, r y ∂(iterKernel P d x)) ^ 2 ∂π
      ≤ (1 / 4 : ℝ) ^ (d / N) * ∫ x, (r x) ^ 2 ∂π := by sorry
