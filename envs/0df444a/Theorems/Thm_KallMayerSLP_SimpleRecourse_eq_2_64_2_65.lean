-- Prove2me | Theorems.Thm_KallMayerSLP_SimpleRecourse_eq_2_64_2_65
-- name    : KallMayerSLP.SimpleRecourse.eq_2_64_2_65
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:13:56.024614+00:00
-- url     : https://prove2.me/theorems/9db60daa-e932-468d-a18e-7f66e8ed6662
-- title:
--   (2.64)–(2.65) — for finite discrete $\tilde\xi$, $G$ is finite discrete with at most $N(2K-1)$ atoms
-- statement:
--   Let the constants satisfy Definition 2.4, and let $\tilde\xi$ have the finite discrete distribution $\{(\xi_\nu,p_\nu);\ \nu=1,\dots,N\}$ with $p_\nu>0$ and $\sum_\nu p_\nu=1$ (2.64). Let $W=\sum_k(\alpha_k+\beta_k)$. Then $G$ is the distribution function of the finite discrete distribution (2.65): the realizations
--
--   $$
--   \xi_\nu\ \text{with}\ \frac{(\alpha_0+\beta_0)p_\nu}{W},\qquad \xi_\nu-u_\kappa\ \text{with}\ \frac{\alpha_\kappa p_\nu}{W},\qquad \xi_\nu+l_\kappa\ \text{with}\ \frac{\beta_\kappa p_\nu}{W}\quad(\kappa=1,\dots,K-1),
--   $$
--
--   which form a probability distribution. It has at most $N(2K-1)$ pairwise different realizations with positive probability.
--
--   So for a finite discrete $\tilde\xi$ the multiple simple recourse problem is a simple recourse problem with a finite discrete distribution, which can be solved as a linear program.
--
--   **Formalization Note** The book writes $\gamma$ for $W$ in (2.65); this is not the $\gamma$ of Definition 2.4.
--
--   Differences from the source:
--   - encoding: F_ξ̃ represents {(ξ_ν, p_ν)} → the law of ξ̃ is Σ_ν p_ν δ_{ξ_ν}; reason: a finite discrete distribution is this sum of point masses
--   - generalization: realizations ξ_1, …, ξ_N of a finite discrete distribution (pairwise different) → ξs : Fin N → ℝ, not required to be injective; reason: coinciding realizations only merge atoms; for distinct ξ_ν it is the printed statement
--   - encoding: γ = Σ_{k=0}^{K−1}(α_k + β_k) in (2.65) → the sum written out (discreteMixtureLaw); reason: the book reuses the letter γ; notation only
--   - encoding: G corresponds to the finite discrete distribution (2.65) → discreteMixtureLaw is a probability measure and its cdf equals mixtureCdf; reason: a distribution corresponds to G exactly when its distribution function is G
--   - reading: at most N·(2K − 1) pairwise different realizations (with positive probabilities) → the measure is concentrated on a finite set of at most N·(2K − 1) points; reason: realizations of zero weight (α₀ + β₀ = 0, α_κ = 0 or β_κ = 0) are not realizations with positive probability; the set of atoms of positive mass has at most N(2K − 1) points
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, (2.64)–(2.65), pp.242–243 (PDF 251–252)

import Mathlib
import Definitions.Def_KallMayerSLP_SimpleRecourse_IsMSRTData
import Definitions.Def_KallMayerSLP_SimpleRecourse_mixtureCdf
import Definitions.Def_KallMayerSLP_SimpleRecourse_discreteMixtureLaw

open MeasureTheory ProbabilityTheory

namespace KallMayerSLP.SimpleRecourse

/-- **(2.64)–(2.65): for a finite discrete `ξ̃`, `G` is finite discrete.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, (2.64)–(2.65), pp.242–243
(PDF 251–252) (Van der Vlerk). If `F_ξ̃` represents a finite discrete distribution
`{(ξ_ν, p_ν); ν = 1, …, N}` with `p_ν > 0 ∀ν`, `Σ_ν p_ν = 1` (2.64), then `G` corresponds to a
finite discrete distribution with at most `N · (2K − 1)` pairwise different realizations (with
positive probabilities). Disregarding possible coincidences of its realizations, it is given by
the realizations and probabilities (2.65) (`discreteMixtureLaw`).

**Formalization Note.** The law of `ξ̃` is `Σ_ν p_ν δ_{ξ_ν}`; realizations are not required to be
distinct. "`G` corresponds to" the distribution (2.65) is: `discreteMixtureLaw` is a probability
measure whose distribution function is `G` (`mixtureCdf`). "At most `N(2K − 1)` pairwise
different realizations with positive probabilities" is: that measure is concentrated on a finite
set of at most `N(2K − 1)` points (zero-weight atoms, possible when `α₀ + β₀ = 0` or some
`α_κ = 0` or `β_κ = 0`, carry no mass and need not be counted). -/
theorem eq_2_64_2_65 {K N : ℕ} (α β u l : Fin K → ℝ) (hd : IsMSRTData K α β u l)
    (p : Fin N → ℝ) (ξs : Fin N → ℝ) (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
    IsProbabilityMeasure (discreteMixtureLaw α β u l p ξs) ∧
    ⇑(cdf (discreteMixtureLaw α β u l p ξs)) =
      mixtureCdf α β u l (∑ i, ENNReal.ofReal (p i) • Measure.dirac (ξs i)) ∧
    ∃ S : Finset ℝ, S.card ≤ N * (2 * K - 1) ∧
      discreteMixtureLaw α β u l p ξs (↑S)ᶜ = 0 := by sorry

end KallMayerSLP.SimpleRecourse
