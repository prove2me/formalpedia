-- Prove2me | Theorems.Thm_FournierGuillin_Conc_lemma_5
-- name    : FournierGuillin.Conc.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:12.14316+00:00
-- url     : https://prove2.me/theorems/439af611-f2f1-468f-89c6-790ed619b940
-- title:
--   Lemma 5, p. 6 — 𝒯_p(μ, ν) ≤ κ_{p,d}𝒟_p(μ, ν) with κ_{p,d} = 2^{p(1+d/2)}(2^p+1)/(2^p−1)
-- statement:
--   Let $d\ge1$ and $p>0$. For all probability measures $\mu,\nu$ on $\mathbb R^d$,
--   $$\mathcal T_p(\mu,\nu)\le\kappa_{p,d}\,\mathcal D_p(\mu,\nu),\qquad \kappa_{p,d}=\frac{2^{p(1+d/2)}(2^p+1)}{2^p-1},$$
--   where $\mathcal T_p$ is the transport cost and $\mathcal D_p$ the multiscale distance of Notation 4(b), built from the shells $B_n$ and the dyadic partitions $\mathcal P_\ell$.
--
--   This is the coupling bound that reduces every estimate on $\mathcal T_p(\mu_N,\mu)$ to estimates on the masses $\mu_N(F)-\mu(F)$ of finitely many boxes at each scale.
--
--   **Formalization Note** No moment assumption is made, as on the page: both sides are valued in $[0,\infty]$ and may be infinite. This milestone is stated identically in the companion mission I (Theorem 1); the duplication is deliberate.
-- source:
--   Fournier & Guillin, arXiv:1312.2128v1, Lemma 5, p. 6; proof pp. 6–7

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_FournierGuillin_Conc_Setting
open MeasureTheory WassersteinDRO.Duality
open scoped ENNReal NNReal

namespace FournierGuillin.Conc

/-- Lemma 5 (Fournier–Guillin, arXiv:1312.2128v1, p. 6): for `d ≥ 1`, `p > 0` and all
probability measures `μ, ν` on `ℝ^d`, `𝒯_p(μ, ν) ≤ κ_{p,d} 𝒟_p(μ, ν)` with
`κ_{p,d} = 2^{p(1+d/2)}(2^p + 1)/(2^p - 1)`. No FournierGuillin.Moment.moment assumption: both sides may be `⊤`. -/
theorem lemma_5 (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : 0 < p)
    (μ ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    FournierGuillin.Moment.transportCost p μ ν ≤ ENNReal.ofReal (kappa d p) * FournierGuillin.Moment.Dp p μ ν := by sorry

end FournierGuillin.Conc
