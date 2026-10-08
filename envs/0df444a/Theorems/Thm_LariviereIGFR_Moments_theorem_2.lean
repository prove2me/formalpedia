-- Prove2me | Theorems.Thm_LariviereIGFR_Moments_theorem_2
-- name    : LariviereIGFR.Moments.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:32:36.422139+00:00
-- url     : https://prove2.me/theorems/9a13f82e-9723-4525-ae80-a608b9c96e4b
-- title:
--   Theorem 2, p. 603 — for IGFR X with support (α, ∞) and g(ξ) → κ ∈ [0, ∞], E[Xⁿ] < ∞ iff κ > n
-- statement:
--   Let $X$ be a nonnegative random variable with distribution $\Phi$, regular density $\phi$, survival function $\bar\Phi=1-\Phi$, failure rate $h=\phi/\bar\Phi$ and generalized failure rate $g(\xi)=\xi h(\xi)$. Suppose that
--
--   1. $X$ has support $(\alpha,\infty)$ for some $\alpha\ge 0$, i.e. $\Phi(\xi)=0$ exactly for $\xi\le\alpha$ and $\Phi(\xi)<1$ for all $\xi$;
--   2. $X$ is IGFR: $g$ is weakly increasing;
--   3. $\lim_{\xi\to\infty}g(\xi)=\kappa$, where $\kappa\in[0,\infty]$ is possibly infinite.
--
--   Then for every real $n>0$,
--   $$
--   \mathbb E[X^n]<\infty\iff\kappa>n .
--   $$
--
--   The theorem is the IGFR analogue of the fact that IFR laws have finite moments of all orders: the limit of the generalized failure rate is exactly the threshold of finite moments. It generalizes Lemma 2 of Lariviere and Porteus (2001); for instance, a finite mean forces $g$ to exceed one eventually, the condition needed for a finite optimal price in the pricing problem that motivates IGFR laws.
--
--   **Formalization Note** $X$ is represented by its law; $\kappa$ is an extended nonnegative real and the limit is taken of $g$ coerced to $[0,\infty]$ (valid since $g\ge 0$), so the case $\kappa=\infty$ (all moments finite) is included. The moment is the $[0,\infty]$-valued integral `nthMoment`, so "finite" is not trivially true. The density is the version that is the derivative of $\Phi$ on the support and $0$ to its left. The nonnegativity hypothesis $\mu((-\infty,0))=0$ is implied by the support hypothesis and is kept for uniformity with the other items. The equivalence includes the boundary case $n=\kappa$, which the printed proof (with $0<\varepsilon<n-\kappa$) does not treat but which is part of the statement.
-- source:
--   Lariviere, A note on probability distributions with increasing generalized failure rates, Oper. Res. 54(3) (2006), p. 603, Theorem 2

import Mathlib
import Definitions.Def_LariviereIGFR_Moments_Setting

namespace LariviereIGFR.Moments

open MeasureTheory ProbabilityTheory Filter Topology

/-- Theorem 2 (Lariviere 2006, p. 603): let `X` be IGFR with support `(α, ∞)` and
`lim_{ξ→∞} g(ξ) = κ ∈ [0, ∞]`. For `n > 0`, `𝔼[Xⁿ]` is finite if and only if `κ > n`. -/
theorem theorem_2 (μ : Measure ℝ) [IsProbabilityMeasure μ] (φ : ℝ → ℝ)
    (hnn : μ (Set.Iio 0) = 0) (hφ : LariviereIGFR.Char.IsRegDensity μ φ)
    (α : ℝ) (hsupp : HasSupportIoi μ α) (higfr : LariviereIGFR.Char.IsIGFR μ φ) (κ : ENNReal)
    (hκ : Tendsto (fun ξ => ENNReal.ofReal (LariviereIGFR.Char.genFailureRate μ φ ξ)) atTop (𝓝 κ))
    (n : ℝ) (hn : 0 < n) :
    nthMoment μ n < ⊤ ↔ ENNReal.ofReal n < κ := by sorry

end LariviereIGFR.Moments
