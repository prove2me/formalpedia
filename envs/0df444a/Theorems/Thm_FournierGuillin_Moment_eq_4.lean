-- Prove2me | Theorems.Thm_FournierGuillin_Moment_eq_4
-- name    : FournierGuillin.Moment.eq_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:23:17.212398+00:00
-- url     : https://prove2.me/theorems/9c847e98-8a97-4867-a064-fb5589e16d44
-- title:
--   Display (4), p. 8 — E𝒟_p(μ_N, μ) ≤ C Σ_n 2^{pn} Σ_ℓ 2^{−pℓ} min{2^{−qn}, 2^{dℓ/2}(2^{−qn}/N)^{1/2}}
-- statement:
--   Let $d\ge1$ and $0<p<q$. There is a constant $C$, depending only on $p,d,q$, such that for every probability measure $\mu$ on $\mathbb R^d$ with $M_q(\mu)=1$ and every $N\ge1$,
--   $$\mathbb E\big(\mathcal D_p(\mu_N,\mu)\big)\le C\sum_{n\ge0}2^{pn}\sum_{\ell\ge0}2^{-p\ell}\min\Big\{2^{-qn},\,2^{d\ell/2}\big(2^{-qn}/N\big)^{1/2}\Big\},$$
--   where $\mu_N$ is the empirical measure of $N$ i.i.d. samples from $\mu$ and $\mathcal D_p$ is the multiscale distance of Notation 4.
--
--   This is the explicit, deterministic double series to which the proof of Theorem 1 reduces; the remaining steps sum it in each regime of $p$ versus $d/2$.
--
--   **Formalization Note** $C$ is chosen after $p,d,q$ and before $\mu$ and $N$. The expectation is a lower Lebesgue integral under $\mu^{\otimes N}$ and both sides are in $[0,\infty]$; the normalization $M_q(\mu)=1$ is the page's own (scaling reduction, p. 8).
-- source:
--   Fournier & Guillin, arXiv:1312.2128v1, Proof of Theorem 1, display (4), p. 8

import Mathlib
import Definitions.Def_WassersteinLinOpt_Ball_wassersteinDist
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_FournierGuillin_Moment_Setting

open MeasureTheory
open scoped ENNReal

namespace FournierGuillin.Moment

/-- Display (4), p. 8: for `p > 0`, `q > p` there is `C` (depending only on `p, d, q`) such that for every
`μ ∈ P(ℝᵈ)` with `M_q(μ) = 1` and every `N ≥ 1`,
`E 𝒟_p(μ_N, μ) ≤ C Σ_{n≥0} 2^{pn} Σ_{ℓ≥0} 2^{−pℓ} min{2^{−qn}, 2^{dℓ/2}(2^{−qn}/N)^{1/2}}`. -/
theorem eq_4 {d : ℕ} (hd : 1 ≤ d) {p q : ℝ} (hp : 0 < p) (hpq : p < q) :
    ∃ C : ℝ, ∀ (μ : Measure (EuclideanSpace ℝ (Fin d))), IsProbabilityMeasure μ →
      moment q μ = 1 → ∀ N : ℕ, 1 ≤ N →
        ∫⁻ ω, Dp p (WassersteinDRO.Duality.empiricalDistribution ω) μ
            ∂(Measure.pi fun _ : Fin N => μ)
          ≤ ENNReal.ofReal C *
            ∑' n : ℕ, ENNReal.ofReal (2 ^ (p * n)) *
              ∑' ℓ : ℕ, ENNReal.ofReal ((2 : ℝ) ^ (-(p * ℓ)) *
                min ((2 : ℝ) ^ (-(q * n))) ((2 : ℝ) ^ ((d : ℝ) * ℓ / 2) * ((2 : ℝ) ^ (-(q * n)) / N) ^ (1 / 2 : ℝ))) := by sorry

end FournierGuillin.Moment
