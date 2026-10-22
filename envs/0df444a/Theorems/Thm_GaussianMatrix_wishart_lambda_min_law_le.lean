-- Prove2me | Theorems.Thm_GaussianMatrix_wishart_lambda_min_law_le
-- name    : GaussianMatrix.wishart_lambda_min_law_le
-- status  : Open
-- author  : @WillR
-- created : 2026-10-21T06:41:04.68419+00:00
-- url     : https://prove2.me/theorems/d094b839-a36e-46d9-b53f-869315181b30
-- title:
--   Edelman domination of the law of the smallest eigenvalue of a real Wishart matrix
-- statement:
--   Let $G\in\mathbb R^{r\times k}$ be a standard Gaussian matrix with
--   $1\le r\le k$, and let $\lambda_{\min}$ be the smallest eigenvalue of the
--   real Wishart matrix $W=GG^\top$.  Put
--   $$a=\frac{k-r-1}{2},\qquad
--   c_{r,k}=\frac{2^{a}\Gamma\!\big(\frac{k+1}{2}\big)}
--   {\Gamma\!\big(\frac r2\big)\Gamma(k-r+1)} .$$
--
--   Then for every measurable $s\subseteq\mathbb R$,
--   $$\mathbb P\{\lambda_{\min}(W)\in s\}\le
--   \int_{s\cap(0,\infty)} c_{r,k}\,l^{a}e^{-l/2}\,dl .$$
--
--   Equivalently, the law of $\lambda_{\min}(W)$ is dominated by the measure
--   with density $c_{r,k}\lambda^{a}e^{-\lambda/2}$ on $(0,\infty)$.  Taking
--   $s=(0,t]$ gives Edelman's integrated density bound
--   $\mathbb P\{\lambda_{\min}\le t\}\le\int_0^t c_{r,k}\lambda^ae^{-\lambda/2}\,d\lambda$,
--   which is the open target `wishart_lambda_min_cdf_density_bound`
--   (`86a4ed0c`).
--
--   **Proof idea (Edelman 1988; Muirhead 2002).**  The ordered eigenvalues of a
--   real Wishart matrix have joint density
--   $$p(l_1,\dots,l_r)=C_{r,k}\prod_{i=1}^r l_i^{a}e^{-l_i/2}
--    \prod_{1\le i<j\le r}(l_j-l_i)$$
--   on $0<l_1<\dots<l_r$.  Integrating $l_2,\dots,l_r$ over
--   $l<l_2<\dots<l_r$ gives
--   $f(l)=K\,l^{a}e^{-l/2}I(l)$ with
--   $$I(l)=\int_{l<\mu_2<\dots<\mu_r}
--    \prod_{i\ge2}\mu_i^{a}e^{-\mu_i/2}
--    \prod_{i<j,\ i,j\ge2}(\mu_j-\mu_i)\,d\mu .$$
--   The integrand is nonnegative and the domain shrinks as $l$ grows, so $I$ is
--   nonincreasing; normalising at $l=0^+$ gives
--   $f(l)=c_{r,k}\,l^{a}e^{-l/2}h(l)$ with $h$ nonincreasing and $h(0^+)=1$,
--   hence $f(l)\le c_{r,k}\,l^{a}e^{-l/2}$.
--
--   For $r=1$ this is an equality: the law of $\lambda_{\min}$ is the
--   chi-square law, proved on the platform as `wishart_lambda_min_cdf_rank_one`
--   (`92f2aae5`) by reducing the $k$-dimensional Gaussian integral with polar
--   coordinates.  For $r\ge2$ the reduction needs the joint eigenvalue density
--   above, which Mathlib does not have.
--
--   **Companion result.**  The purely analytic half of the Tropp-Webber lower
--   tail is already Proved: `density_integral_le_tail_bound` (`fbf09435`) gives
--   $$\int_0^t c_{r,k}\lambda^{a}e^{-\lambda/2}\,d\lambda
--   \le\frac{1}{\Gamma(k-r+2)}\Big(\frac{t(k+r)}{2}\Big)^{(k-r+1)/2}.$$
--   With the present theorem this yields `86a4ed0c`, and hence
--   `wishart_lambda_min_tail` (`4939bb72`), `pinv_spectral_tail`
--   (`c927004d`), `pinv_spectral_expectation` (`d4d3ca6e`) and
--   `inverse_wishart_spectral_moment` (`b8bbfa46`).
-- source:
--   Gaussian Random Matrices II mission 1dfc2230-f260-4532-b3f9-7d60b9f4b139; root leaf 86a4ed0c-832c-4bb5-a8d7-efc12b3a4f57 wishart_lambda_min_cdf_density_bound; declared child chain 4939bb72 -> c927004d -> d4d3ca6e -> b8bbfa46

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix
open GaussianMatrix

namespace GaussianMatrix

/-- The law of the smallest eigenvalue of a real Wishart matrix, in density form.

Let `G` be an `r x k` standard Gaussian matrix with `1 <= r <= k`, let
`W = G * Gᵀ`, and let `λ_min(W) = sMin (Matrix.of G)ᵀ ^ 2`.  Write

$$
a=\frac{k-r-1}{2},\qquad
c_{r,k}=\frac{2^{a}\,\Gamma\!\big(\frac{k+1}{2}\big)}
{\Gamma\!\big(\frac r2\big)\,\Gamma(k-r+1)} .
$$

The law of `λ_min(W)` is the measure on `ℝ` with density
`c_{r,k} l^a e^{-l/2}` on `(0, ∞)`; i.e. for every measurable `s ⊆ ℝ`,

$$
\mathbb P\{\lambda_{\min}(W)\in s\}
=\int_{s\cap(0,\infty)} c_{r,k}\,l^{a}e^{-l/2}\,dl .
$$

**Why this is the right statement.**  It is strictly stronger than the
parent `wishart_lambda_min_cdf_density_bound` (`86a4ed0c`), which asks only
for the single-set bound `\mathbb P\{\lambda_{\min}\le t\}`; and it is
*false* as stated for `r = 1`, where the density of `λ_min` is the
chi-square density `l^{(k-2)/2} e^{-l/2}/(2^{k/2} Γ(k/2))` and
`c_{1,k} = 1/(2^{k/2} Γ(k/2))` — so the `r = 1` case coincides, but for
`r >= 2` the density of `λ_min` is
`c_{r,k} l^a e^{-l/2} h(l)` with `h` **nonincreasing** and `h(0⁺) = 1`, and
it is only the *domination* `h(l) <= 1` that gives Edelman's inequality.

Accordingly the correct child statement is the **Edelman domination of the
density**: the law of `λ_min(W)` is dominated, in the sense of lower
Lebesgue integrals, by the measure with density `c_{r,k} l^a e^{-l/2}`:

$$
\mathbb P\{\lambda_{\min}(W)\in s\}
\le \int_{s\cap(0,\infty)} c_{r,k}\,l^{a}e^{-l/2}\,dl
\qquad\text{for every measurable } s\subseteq\mathbb R .
$$

Taking `s = (0, t]` yields the parent.

**Why the domination holds.**  The ordered eigenvalues of a real Wishart
matrix have joint density
`p(l_1, …, l_r) = C_{r,k} ∏_i l_i^a e^{-l_i/2} ∏_{i<j} (l_j-l_i)` on the
ordered cone `0 < l_1 < … < l_r` (Muirhead 2002; Edelman 1988).
Integrating `l_2, …, l_r` over `l < l_2 < … < l_r` gives
`f(l) = K l^a e^{-l/2} I(l)` with
`I(l) = ∫_{l<μ_2<…<μ_r} ∏_{i≥2} μ_i^a e^{-μ_i/2} ∏_{i<j, i,j≥2} (μ_j-μ_i) dμ`.
The integrand is nonnegative and the domain shrinks as `l` grows, so `I` is
nonincreasing, whence `h(l) = K I(l) / (K I(0⁺))` is nonincreasing with
`h(0⁺) = 1` and `f(l) = c_{r,k} l^a e^{-l/2} h(l) <= c_{r,k} l^a e^{-l/2}`.

For `r = 1` the inequality is an equality: the law of `λ_min` is the
chi-square law, which the platform proves as
`wishart_lambda_min_cdf_rank_one` (`92f2aae5`) by reducing the
`k`-dimensional Gaussian integral with polar coordinates.

**Formalisation note.**  In Lean the statement should be: the push forward
of `gaussianMatrix r k` by `G ↦ sMin (Matrix.of G)ᵀ ^ 2` is bounded below,
on every measurable set, by `volume.withDensity (fun l => ENNReal.ofReal
(c_{r,k} * l^a * Real.exp (-l/2)))` restricted to `Set.Ioi 0`. -/
theorem wishart_lambda_min_law_le {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k)
    (s : Set ℝ) (hs : MeasurableSet s) :
    (gaussianMatrix r k) {G : Fin r → Fin k → ℝ |
        sMin (Matrix.of G)ᵀ ^ 2 ∈ s}
      ≤ ∫⁻ x in s ∩ Set.Ioi (0 : ℝ), ENNReal.ofReal
          (2 ^ (((k : ℝ) - r - 1) / 2) * Real.Gamma (((k : ℝ) + 1) / 2)
              / (Real.Gamma ((r : ℝ) / 2) * Real.Gamma ((k : ℝ) - r + 1))
            * x ^ (((k : ℝ) - r - 1) / 2) * Real.exp (-x / 2)) := by
  sorry

end GaussianMatrix
