-- Prove2me | Theorems.Thm_MarkovChainCLT_abs_integral_sub_le_sqrt_tvDist_mul
-- name    : MarkovChainCLT.abs_integral_sub_le_sqrt_tvDist_mul
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T22:49:23.341977+00:00
-- url     : https://prove2.me/theorems/74badda5-b400-48bb-b1a0-235893f09abd
-- title:
--   Square-root total-variation bound for $L^2$ test functions
-- statement:
--   **A square-root total-variation bound for square-integrable test functions.** For probability measures $\mu,\nu$ and a measurable $h$ with $h^2$ integrable against both,
--   $$\Bigl|\int h\,d\mu - \int h\,d\nu\Bigr| \;\le\; \sqrt{\|\mu-\nu\|}\;\Bigl(\|h\|_{L^2(\mu)} + \|h\|_{L^2(\nu)}\Bigr),$$
--   where $\|\mu-\nu\| = \sup_A|\mu(A)-\nu(A)|$.
--
--   **Why the square root, and why this is the right inequality.** For a *bounded* $h$ the elementary bound $|\int h\,d\mu - \int h\,d\nu| \le 2\|h\|_\infty\|\mu-\nu\|$ is linear in the total variation, but it is useless when $h$ is merely square-integrable. Replacing $\|h\|_\infty$ by $\|h\|_{L^2}$ costs a square root — and that is exactly the trade one needs, because $\sqrt{\|\mu-\nu\|}$ still decays geometrically when $\|\mu-\nu\|$ does.
--
--   **The application: $L^2$ contraction for uniformly ergodic chains.** Let $P$ be uniformly ergodic with invariant law $\pi$, so $\sup_x\|P^N(x,\cdot)-\pi\| \le \rho$ with $\rho$ as small as we like. For $h\in L^2(\pi)$ with $\int h\,d\pi = 0$, applying the inequality with $\mu = P^N(x,\cdot)$ and $\nu=\pi$ and then squaring and integrating in $x$ against $\pi$ — using the invariance $\int\!\!\int h^2\,dP^N(x,\cdot)\,d\pi(x) = \int h^2 d\pi$ — gives
--   $$\|P^Nh\|_{L^2(\pi)} \;\le\; 2\sqrt{\rho}\;\|h\|_{L^2(\pi)} .$$
--   Choosing $N$ with $\rho < 1/4$ makes $P^N$ a strict contraction on the mean-zero subspace of $L^2(\pi)$, which is what makes the Neumann series $\hat g = \sum_{n\ge0}P^n(f-\pi f)$ converge and solves the Poisson equation $\hat g - P\hat g = f - \pi f$ for every square-integrable $f$. Without this step the martingale approximation underlying the Markov chain CLT is available only for bounded $f$.
--
--   **Proof.** Let $A$ be a Hahn set for $\mu-\nu$, so $\nu \le \mu$ on subsets of $A$ and $\mu \le \nu$ on subsets of $A^c$. Then $\rho_1 := (\mu-\nu)|_A$ and $\rho_2 := (\nu-\mu)|_{A^c}$ are *positive* measures with
--   $$\int h\,d\mu - \int h\,d\nu \;=\; \int h\,d\rho_1 - \int h\,d\rho_2,$$
--   and $\rho_1 \le \mu$, $\rho_2 \le \nu$, with masses $\rho_1(X) = \mu(A)-\nu(A) \le \|\mu-\nu\|$ and $\rho_2(X) = \nu(A^c)-\mu(A^c) \le \|\mu-\nu\|$. Cauchy–Schwarz against a finite measure $\rho$ — obtained from the nonnegativity of $\int(|h|-\lambda)^2 d\rho$ at $\lambda = \int|h|\,d\rho\,/\,\rho(X)$ — gives $|\int h\,d\rho| \le \sqrt{\rho(X)}\,\sqrt{\int h^2 d\rho}$. Applying this to $\rho_1$ and $\rho_2$, and using monotonicity of the second moment in the measure, yields the two terms of the bound.
-- source:
--   S. P. Meyn and R. L. Tweedie, Markov Chains and Stochastic Stability, 2nd ed., Cambridge 2009, Ch. 16 and Theorem 16.0.2; L. Tierney, "Markov Chains for Exploring Posterior Distributions", Annals of Statistics 22 (1994) 1701-1728; G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, Section 2.

import Definitions.Def_TotalVariationDist
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory
open MarkovChainCLT
open scoped ENNReal NNReal

theorem MarkovChainCLT.abs_integral_sub_le_sqrt_tvDist_mul {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : X → ℝ)
    (hh : Measurable h) (hμ : Integrable (fun x => (h x) ^ 2) μ)
    (hν : Integrable (fun x => (h x) ^ 2) ν) :
    |∫ x, h x ∂μ - ∫ x, h x ∂ν|
      ≤ Real.sqrt (tvDist μ ν) *
        (Real.sqrt (∫ x, (h x) ^ 2 ∂μ) + Real.sqrt (∫ x, (h x) ^ 2 ∂ν)) := by sorry
