-- Prove2me | Theorems.Thm_KallMayerSLP_GenConcave_theorem_2_8
-- name    : KallMayerSLP.GenConcave.theorem_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:11:35.896999+00:00
-- url     : https://prove2.me/theorems/d4e18cdf-844e-4749-8116-cc97e6edf967
-- title:
--   Theorem 2.8 — a $\gamma$-concave density induces a $\gamma/(1+r\gamma)$-concave probability measure
-- statement:
--   Let $\xi$ be an $r$-dimensional random vector ($r\ge1$) whose probability distribution $\mathbb P_\xi$ has a probability density function $f$, and let $-1/r\le\gamma\le\infty$. If $f$ is $\gamma$-concave, that is,
--
--   $$
--   f(\lambda x+(1-\lambda)y)\ \ge\ \mathcal M_\gamma^\lambda\bigl(f(x),f(y)\bigr)\qquad\text{for all }x,y\in\mathbb R^r,\ \lambda\in[0,1],
--   $$
--
--   then $\mathbb P_\xi$ is a $\dfrac{\gamma}{1+r\gamma}$-concave probability measure: for all convex Borel sets $A,B\subseteq\mathbb R^r$ and $\lambda\in[0,1]$ with $\lambda A+(1-\lambda)B$ Borel,
--
--   $$
--   \mathbb P_\xi\bigl(\lambda A+(1-\lambda)B\bigr)\ \ge\ \mathcal M^\lambda_{\gamma/(1+r\gamma)}\bigl(\mathbb P_\xi(A),\mathbb P_\xi(B)\bigr).
--   $$
--
--   Here $\gamma/(1+r\gamma)=-\infty$ at $\gamma=-1/r$ and $=1/r$ at $\gamma=\infty$.
--
--   This is Borell's theorem (1975; Prékopa 1971–73 for $\gamma=0$). With Proposition 2.2 it shows that the distribution function of $\xi$ is $\gamma/(1+r\gamma)$-concave, so the joint probability constraint $\mathbb P(Tx\ge\xi)\ge\alpha$ defines a convex set: log-concave densities (uniform on a convex set, non-degenerate normal, Dirichlet, …) give log-concave distribution functions, and densities with $f^{-1/r}$ convex give quasi-concave ones.
--
--   **Formalization Note** $\mathbb R^r$ is `Fin r → ℝ`. "$f$ is a probability density of $\mathbb P_\xi$" is $\mathbb P_\xi=\int f\,d\lambda^r$ (`volume.withDensity`) together with $\mathbb P_\xi$ being a probability measure; nonnegativity of $f$ is part of $\gamma$-concavity, which holds at every pair of points. Exponents are extended reals.
--
--   Differences from the source:
--   - encoding: "$f$ a probability density function for the distribution of $\xi$" → $\mu=$ `volume.withDensity f` with $\mu$ a probability measure; reason: Lean convention, same instances (every law is a measure on $\mathbb R^r$)
--   - generalization: a density function (measurable) → no measurability hypothesis on $f$; reason: a $\gamma$-concave function is quasi-concave, hence Lebesgue measurable, and every density in the book's sense is covered
--   - encoding: $r$-dimensional with $-1/r\le\gamma$ → $r\ge1$; reason: the hypothesis $-1/r\le\gamma$ presupposes $r\ge1$
--   - encoding: $\gamma/(1+r\gamma)$ at $\gamma=-1/r$ and $\gamma=\infty$ → $-\infty$ and $1/r$; reason: the formula is undefined there; the limits are the values of Figure 2.6 (paper reading 4)
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, Theorem 2.8, p.127 (PDF 137); Definitions 2.3–2.4, pp.123–126 (PDF 133–136); Figure 2.6, p.128 (PDF 138)

import Mathlib
import Definitions.Def_KallMayerSLP_GenConcave_concavityExponent
import Definitions.Def_KallMayerSLP_GenConcave_IsGammaConcaveFun
import Definitions.Def_KallMayerSLP_GenConcave_IsGammaConcaveMeasure

open MeasureTheory

namespace KallMayerSLP.GenConcave

/-- **Theorem 2.8** (Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2,
Theorem 2.8, p. 127, PDF p. 137; Borell 1975). Let `f` be a `γ`-concave probability density
function for the probability distribution of the `r`-dimensional random variable `ξ`. Let
`−1/r ≤ γ ≤ ∞`. Then `ℙ_ξ` is a `γ/(1 + rγ)`-concave probability measure.

**Formalization Note.** The law `ℙ_ξ` is the measure `μ` on `ℝ^r = Fin r → ℝ`; "`f` is a
probability density function for `ℙ_ξ`" is `μ = volume.withDensity f` together with `μ`
being a probability measure (`∫ f = 1`); nonnegativity of `f` is part of `γ`-concavity.
`γ`-concavity of `f` holds at every pair of points (Definition 2.3). `r ≥ 1`, as the
hypothesis `−1/r ≤ γ` presupposes. `γ ∈ EReal`, and `γ/(1 + rγ)` is `concavityExponent r γ`,
equal to `−∞` (quasi-concavity) at `γ = −1/r` and to `1/r` at `γ = ∞` (Figure 2.6, p. 128).
No measurability of `f` is assumed: a `γ`-concave function is quasi-concave, so it is
Lebesgue measurable and `withDensity` is the usual density measure. -/
theorem theorem_2_8 {r : ℕ} (hr : 0 < r) (γ : EReal)
    (hγ : (((-1 : ℝ) / r : ℝ) : EReal) ≤ γ) (f : (Fin r → ℝ) → ℝ)
    (hf : IsGammaConcaveFun γ f) (μ : Measure (Fin r → ℝ))
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (f x))) [IsProbabilityMeasure μ] :
    IsGammaConcaveMeasure (concavityExponent r γ) μ := by sorry

end KallMayerSLP.GenConcave
