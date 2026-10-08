-- Prove2me | Theorems.Thm_FournierGuillin_Conc_proposition_10
-- name    : FournierGuillin.Conc.proposition_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:15.503612+00:00
-- url     : https://prove2.me/theorems/25013542-724a-4e41-a235-247957043510
-- title:
--   Proposition 10, p. 12 — ℙ[𝒟_p(μ_N, μ) ≥ x] ≤ 1_{x≤1}C exp(−cNx²), exp(−cN(x/log(2+1/x))²) or exp(−cNx^{d/p}) for compact μ
-- statement:
--   Let $d\ge1$ and $p>0$. There are constants $C,c>0$, depending only on $p$ and $d$, such that for every probability measure $\mu$ supported in $(-1,1]^d$, every integer $N\ge1$ and every $x>0$,
--   $$\mathbb P\big[\mathcal D_p(\mu_N,\mu)\ge x\big]\le\mathbf 1_{\{x\le1\}}\,C\times\begin{cases}\exp(-cNx^2)&p>d/2,\\ \exp\big(-cN(x/\log(2+1/x))^2\big)&p=d/2,\\ \exp(-cNx^{d/p})&p\in(0,d/2),\end{cases}$$
--   where $\mu_N$ is the empirical measure of $N$ i.i.d. $\mu$-distributed points and $\mathcal D_p$ is the compact distance of Notation 4(a).
--
--   This is the compact version of Theorem 2, obtained from Proposition 8 by depoissonization.
--
--   **Formalization Note** The sample is $\omega=(X_1,\dots,X_N)$ under the product measure $\mu^{\otimes N}$; the probability is that measure applied to the event (an outer measure, should the event fail to be measurable; it is measurable in fact, so this is the page's quantity). The proposition is posed for every $p>0$, as printed; the third branch of the rate is the page's $p\in(0,d/2)$.
-- source:
--   Fournier & Guillin, arXiv:1312.2128v1, Proposition 10, p. 12; proof pp. 13–14

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_FournierGuillin_Conc_Setting
open MeasureTheory WassersteinDRO.Duality
open scoped ENNReal NNReal

namespace FournierGuillin.Conc

/-- Proposition 10 (p. 12): for `μ` supported in `(-1, 1]^d` there are `C, c > 0` depending only on
`p, d` such that for all `N ≥ 1` and `x > 0`,
`ℙ[𝒟_p(μ_N, μ) ≥ x] ≤ 1_{x ≤ 1} C a(N, x)/C` (`rateA`), with `𝒟_p` the compact distance `Dcube`.
Posed for every `p > 0`, as printed; the third branch of `rateA` is the page's `p ∈ (0, d/2)`. -/
theorem proposition_10 (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : 0 < p) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ], μ (FournierGuillin.Moment.shell 0)ᶜ = 0 →
        ∀ N : ℕ, 1 ≤ N → ∀ x : ℝ, 0 < x →
          Measure.pi (fun _ : Fin N => μ)
              {ω | ENNReal.ofReal x ≤ FournierGuillin.Moment.Dcube p (empiricalDistribution ω) μ} ≤
            ENNReal.ofReal ((if x ≤ 1 then 1 else 0) * C * rateA d p c N x) := by sorry

end FournierGuillin.Conc
