-- Prove2me | Theorems.Thm_FournierGuillin_Moment_theorem_1
-- name    : FournierGuillin.Moment.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:23:04.104984+00:00
-- url     : https://prove2.me/theorems/d9438e14-ef19-4715-8285-79cd5f7bfdfa
-- title:
--   Theorem 1, p. 2 — E 𝒯_p(μ_N, μ) ≤ C M_q^{p/q}(μ)(N^{−1/2}, N^{−1/2}log(1+N) or N^{−p/d}, + N^{−(q−p)/q})
-- statement:
--   Let $d\ge1$, let $\mu$ be a probability measure on $\mathbb R^d$, let $X_1,X_2,\dots$ be i.i.d. with law $\mu$, and let $\mu_N=\frac1N\sum_{k=1}^N\delta_{X_k}$ be the empirical measure. Let $p>0$ and assume that $M_q(\mu)=\int|x|^q\,\mu(dx)<\infty$ for some $q>p$. There exists a constant $C$ depending only on $p,d,q$ such that, for all $N\ge1$,
--   $$\mathbb E\big(\mathcal T_p(\mu_N,\mu)\big)\le C\,M_q^{p/q}(\mu)\times\begin{cases}N^{-1/2}+N^{-(q-p)/q}&\text{if }p>d/2\text{ and }q\ne2p,\\ N^{-1/2}\log(1+N)+N^{-(q-p)/q}&\text{if }p=d/2\text{ and }q\ne2p,\\ N^{-p/d}+N^{-(q-p)/q}&\text{if }p\in(0,d/2)\text{ and }q\ne dp/(d-p).\end{cases}$$
--   Here $\mathcal T_p(\mu,\nu)$ is the optimal transport cost with cost $|x-y|^p$ (no $1/p$ root) and $|\cdot|$ is the Euclidean norm.
--
--   The theorem gives non-asymptotic rates for the convergence of the empirical measure in Wasserstein distance under a mere moment condition, sharp in general (the paper's examples on pp. 2–3), and is the standard reference rate in statistics, quantization and particle approximations.
--
--   **Formalization Note** The page prints the third case as "$q\ne d/(d-p)$". The remark right below the theorem says the critical value is $q=dp/(d-p)$, and Step 4 of the proof (p. 9) treats exactly $q>dp/(d-p)$ and $q\in(p,dp/(d-p))$; at $q=dp/(d-p)$ the proof gives only $N^{-p/d}\log N$. The two values agree only for $p=1$. The statement therefore excludes $q=dp/(d-p)$. The constant $C$ is chosen after $p,d,q$ and before $\mu$ and $N$. The sample is $(X_1,\dots,X_N)$ under the product measure $\mu^{\otimes N}$ (the first $N$ terms of the i.i.d. sequence), the expectation is the lower Lebesgue integral of the $[0,\infty]$-valued map $\omega\mapsto\mathcal T_p(\mu_N,\mu)$ (which is measurable), and $M_q^{p/q}(\mu)$ is computed from the finite real value of $M_q(\mu)$. When $M_q(\mu)=0$, i.e. $\mu=\delta_0$, both sides are $0$.
-- source:
--   Fournier & Guillin, arXiv:1312.2128v1, Theorem 1, p. 2; remark below it, p. 2; proof §3, pp. 8–9

import Mathlib
import Definitions.Def_WassersteinLinOpt_Ball_wassersteinDist
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_FournierGuillin_Moment_Setting

open MeasureTheory
open scoped ENNReal

namespace FournierGuillin.Moment

/-- Theorem 1, p. 2: let `p > 0` and `q > p`. There is a constant `C` depending only on `p, d, q` such
that for every `μ ∈ P(ℝᵈ)` with `M_q(μ) < ∞` and all `N ≥ 1`,
`E 𝒯_p(μ_N, μ) ≤ C M_q^{p/q}(μ) · rateT1 d p q N`, where the cases are `p > d/2` and `q ≠ 2p`;
`p = d/2` and `q ≠ 2p`; `p ∈ (0, d/2)` and `q ≠ dp/(d − p)`. The page prints `q ≠ d/(d − p)` in the third
case; the remark below the theorem and Step 4 of the proof (p. 9) show the critical value is
`dp/(d − p)`. -/
theorem theorem_1 (d : ℕ) (hd : 1 ≤ d) (p q : ℝ) (hp : 0 < p) (hpq : p < q)
    (h2p : (d : ℝ) / 2 ≤ p → q ≠ 2 * p)
    (hdp : p < (d : ℝ) / 2 → q ≠ d * p / (d - p)) :
    ∃ C : ℝ, ∀ (μ : Measure (EuclideanSpace ℝ (Fin d))), IsProbabilityMeasure μ →
      moment q μ < ⊤ → ∀ N : ℕ, 1 ≤ N →
        ∫⁻ ω, transportCost p (WassersteinDRO.Duality.empiricalDistribution ω) μ
            ∂(Measure.pi fun _ : Fin N => μ)
          ≤ ENNReal.ofReal (C * (moment q μ).toReal ^ (p / q) * rateT1 d p q N) := by sorry

end FournierGuillin.Moment
