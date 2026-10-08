-- Prove2me | Theorems.Thm_FournierGuillin_Moment_lemma_6
-- name    : FournierGuillin.Moment.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:27:07.14098+00:00
-- url     : https://prove2.me/theorems/df255256-30a7-4f01-90d2-d92cbda7e682
-- title:
--   Lemma 6, p. 7 — 𝒟_p(μ, ν) ≤ C Σ_n 2^{pn} Σ_{ℓ≥0} 2^{−pℓ} Σ_{F∈𝒫_ℓ} |μ(2ⁿF ∩ B_n) − ν(2ⁿF ∩ B_n)|
-- statement:
--   Let $p>0$ and $d\ge1$. There is a constant $C$, depending only on $p$ and $d$, such that for all probability measures $\mu,\nu$ on $\mathbb R^d$,
--   $$\mathcal D_p(\mu,\nu)\le C\sum_{n\ge0}2^{pn}\sum_{\ell\ge0}2^{-p\ell}\sum_{F\in\mathcal P_\ell}\big|\mu(2^nF\cap B_n)-\nu(2^nF\cap B_n)\big|,$$
--   where $2^nF=\{2^nx: x\in F\}$, $B_n$ are the dyadic shells and $\mathcal P_\ell$ the dyadic partition of $(-1,1]^d$ at level $\ell$.
--
--   The right side involves only masses of fixed sets, so its expectation under the empirical measure reduces to binomial mean deviations; this is the form of $\mathcal D_p$ used for the moment estimates.
--
--   **Formalization Note** The constant is chosen before $\mu$ and $\nu$. Note that the inner sum here starts at $\ell=0$ (where $2^nF\cap B_n=B_n$), while the definition of $\mathcal D_p$ in the compact case starts at $\ell=1$. All sums are in $[0,\infty]$.
-- source:
--   Fournier & Guillin, arXiv:1312.2128v1, Lemma 6, p. 7

import Mathlib
import Definitions.Def_WassersteinLinOpt_Ball_wassersteinDist
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_FournierGuillin_Moment_Setting

open MeasureTheory
open scoped ENNReal

namespace FournierGuillin.Moment

/-- Lemma 6, p. 7: for `p > 0`, `d ≥ 1` there is a constant `C`, depending only on `p, d`, such that
for all `μ, ν ∈ P(ℝᵈ)`,
`𝒟_p(μ, ν) ≤ C Σ_{n≥0} 2^{pn} Σ_{ℓ≥0} 2^{−pℓ} Σ_{F∈𝒫_ℓ} |μ(2ⁿF ∩ B_n) − ν(2ⁿF ∩ B_n)|`.
`C` is chosen before `μ, ν`. -/
theorem lemma_6 {d : ℕ} (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, ∀ (μ ν : Measure (EuclideanSpace ℝ (Fin d))),
      IsProbabilityMeasure μ → IsProbabilityMeasure ν →
        Dp p μ ν ≤ ENNReal.ofReal C *
          ∑' n : ℕ, ENNReal.ofReal (2 ^ (p * n)) *
            ∑' ℓ : ℕ, ENNReal.ofReal (2 ^ (-(p * ℓ))) *
              ∑ k : Fin d → Fin (2 ^ ℓ),
                ENNReal.ofReal |(μ (scaledCell n ℓ k)).toReal - (ν (scaledCell n ℓ k)).toReal| := by sorry

end FournierGuillin.Moment
