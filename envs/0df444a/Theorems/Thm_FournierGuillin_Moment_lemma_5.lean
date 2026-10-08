-- Prove2me | Theorems.Thm_FournierGuillin_Moment_lemma_5
-- name    : FournierGuillin.Moment.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:26:28.270198+00:00
-- url     : https://prove2.me/theorems/ead96b44-e57c-4a28-80e7-79502ed67fa7
-- title:
--   Lemma 5, p. 6 — 𝒯_p(μ, ν) ≤ κ_{p,d}𝒟_p(μ, ν), κ_{p,d} = 2^{p(1+d/2)}(2^p+1)/(2^p−1)
-- statement:
--   Let $d\ge1$ and $p>0$. For all probability measures $\mu,\nu$ on $\mathbb R^d$,
--   $$\mathcal T_p(\mu,\nu)\le\kappa_{p,d}\,\mathcal D_p(\mu,\nu),\qquad \kappa_{p,d}=\frac{2^{p(1+d/2)}(2^p+1)}{2^p-1}.$$
--   Here $\mathcal T_p$ is the optimal transport cost with cost $|x-y|^p$ and $\mathcal D_p$ is the multiscale dyadic distance of Notation 4(b).
--
--   This is the coupling bound, due essentially to Dereich, Scheutzow and Schottstedt, on which both main theorems of the paper rest: it replaces the transport problem by sums of mass differences over dyadic cells of every scale inside every dyadic shell.
--
--   **Formalization Note** No moment assumption is made: both sides lie in $[0,\infty]$ and may be $+\infty$. The norm is Euclidean, which is the norm for which the page's diameter bound $2^{1+d/2}$ of $(-1,1]^d$ (proof, Step 1) holds.
-- source:
--   Fournier & Guillin, arXiv:1312.2128v1, Lemma 5, p. 6; proof pp. 6–7

import Mathlib
import Definitions.Def_WassersteinLinOpt_Ball_wassersteinDist
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_FournierGuillin_Moment_Setting

open MeasureTheory
open scoped ENNReal

namespace FournierGuillin.Moment

/-- Lemma 5, p. 6: for `d ≥ 1`, `p > 0` and all probability measures `μ, ν` on `ℝᵈ`,
`𝒯_p(μ, ν) ≤ κ_{p,d} 𝒟_p(μ, ν)` with `κ_{p,d} = 2^{p(1+d/2)}(2^p + 1)/(2^p − 1)`. No moment assumption:
both sides may be `⊤`. -/
theorem lemma_5 {d : ℕ} (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p)
    (μ ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    transportCost p μ ν ≤
      ENNReal.ofReal (2 ^ (p * (1 + (d : ℝ) / 2)) * (2 ^ p + 1) / (2 ^ p - 1)) * Dp p μ ν := by sorry

end FournierGuillin.Moment
