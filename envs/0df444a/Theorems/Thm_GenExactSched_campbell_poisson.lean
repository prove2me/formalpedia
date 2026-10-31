-- Prove2me | Theorems.Thm_GenExactSched_campbell_poisson
-- name    : GenExactSched.campbell_poisson
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:44:54.684+00:00
-- url     : https://prove2.me/theorems/b12b8a59-2c33-4759-bfef-10f49a5d6948
-- title:
--   Theorem 7 — Campbell's formula: mean and variance of $\int g\,dN$ for a Poisson random measure (corrected: $g\in L^1\cap L^2$)
-- statement:
--   Let $N$ be a Poisson random measure on a measurable space $E$ with σ-finite intensity $\nu$, over a probability space $(\Omega,\mathbb P)$. Then:
--
--   1. for every measurable $c:E\to[0,\infty]$,
--   $$\mathbb E\Big[\int_E c\,dN\Big]=\int_E c\,d\nu;$$
--   2. for every measurable $g:E\to\mathbb R$ with $\int|g|\,d\nu<\infty$ and $\int g^2\,d\nu<\infty$, the random sum $G=\int g\,dN=\sum_k g(x_k)$ converges absolutely almost surely, and
--   $$\mathbb E[G]=\int_E g\,d\nu,\qquad \mathrm{Var}(G)=\int_E g^2\,d\nu.$$
--
--   This is the process-level fact behind the whole paper: applied to the service rates of the jobs present at time $t$, it gives the mean and variance of the service capacity (Lemma 2), and applied to per-job penalties it gives the long-run penalty rates (81).
--
--   **Formalization Note** The paper's independently marked Poisson process on $\mathbb R^d$ with marks in $\mathbb R^p$ is a Poisson random measure on $\mathbb R^d\times\mathbb R^p$ with intensity $\Lambda\otimes F$. Absolute convergence is integrability of $g$ against $N_\omega$; the variance is the $[0,\infty]$-valued variance.
--
--   Differences from the source:
--   - correction: g measurable with ∫∫ g² Λ(dx)F(dz) < ∞ → g measurable with ∫ |g| dν < ∞ and ∫ g² dν < ∞; reason: square integrability does not give absolute convergence: Lebesgue intensity on [1, ∞) and g(x) = 1/x have ∫ g² = 1 but Σ_k 1/x_k = ∞ a.s. (paper.md item 3).
--   - generalization: independently marked Poisson point process on ℝ^d with marks in ℝ^p of law F → Poisson random measure on any measurable space E with σ-finite intensity ν; reason: the marked process is a Poisson random measure on ℝ^d × ℝ^p with intensity Λ ⊗ F; the statement specializes to it.
--   - generalization: mean and variance for square-integrable g only → also E[∫ c dN] = ∫ c dν for every measurable c : E → [0, ∞]; reason: an added conclusion (Campbell's first-moment formula for nonnegative functions), needed for the penalty rates; the paper's clauses are unchanged.
--   - encoding: random sum G = Σ_k g(x_k), absolutely convergent with probability one → G(ω) = ∫ g dN(ω) (Bochner integral), with g integrable against N(ω) for a.e. ω; Var as Mathlib's evariance; reason: the integral against the counting measure of the points is the sum, and integrability is absolute convergence.
-- source:
--   Nakahira–Ferragut–Wierman, Generalized Exact Scheduling: A Minimal-Variance Distributed Deadline Scheduler, arXiv:2004.12280v2, Appendix A, Theorem 7, p. 38

import Mathlib
import Definitions.Def_GenExactSched_PoissonRandomMeasure

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GenExactSched

/-- **Campbell's formula for a Poisson random measure (Theorem 7, corrected)**,
Nakahira–Ferragut–Wierman, arXiv:2004.12280v2, Appendix A, Theorem 7, p. 38.

Let `N` be a Poisson random measure on `E` with σ-finite intensity `ν`. Then

1. for every measurable `c : E → [0, ∞]`, `E[∫ c dN] = ∫ c dν`;
2. for every measurable `g : E → ℝ` with `∫ |g| dν < ∞` and `∫ g² dν < ∞`: almost surely
   `∫ |g| dN < ∞` (the random sum `G = Σ_k g(x_k)` converges absolutely), `E[G] = ∫ g dν`, and
   `Var(G) = ∫ g² dν`.

**Formalization Note.** The paper's independently marked Poisson process on `ℝ^d` with marks in
`ℝ^p` is a Poisson random measure on the product, so a general `E` covers it. The printed
hypothesis is `∫ g² < ∞` only; it does not give absolute convergence (Lebesgue intensity on
`[1, ∞)`, `g(x) = 1/x`), so `∫ |g| dν < ∞` is added. Sums over points are integrals against
`N ω`; the variance is Mathlib's `ℝ≥0∞`-valued `evariance`. -/
theorem campbell_poisson {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure E) [SigmaFinite ν]
    (N : Ω → Measure E) (hN : IsPoissonRandomMeasure P ν N) :
    (∀ c : E → ℝ≥0∞, Measurable c → ∫⁻ ω, ∫⁻ x, c x ∂(N ω) ∂P = ∫⁻ x, c x ∂ν) ∧
    (∀ g : E → ℝ, Measurable g → Integrable g ν → Integrable (fun x => g x ^ 2) ν →
      (∀ᵐ ω ∂P, Integrable g (N ω)) ∧
      ∫ ω, (∫ x, g x ∂(N ω)) ∂P = ∫ x, g x ∂ν ∧
      evariance (fun ω => ∫ x, g x ∂(N ω)) P = ENNReal.ofReal (∫ x, g x ^ 2 ∂ν)) := by sorry

end GenExactSched
