-- Prove2me | Theorems.Thm_FournierGuillin_Moment_level_bound
-- name    : FournierGuillin.Moment.level_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:23:07.338106+00:00
-- url     : https://prove2.me/theorems/4d1ffe70-bf18-42d3-97d4-1ab6459eeb68
-- title:
--   Proof of Theorem 1, p. 8 — Σ_{F∈𝒫_ℓ} E|μ_N(2ⁿF∩B_n) − μ(2ⁿF∩B_n)| ≤ min{2μ(B_n), 2^{dℓ/2}(μ(B_n)/N)^{1/2}}
-- statement:
--   Let $d\ge1$, let $\mu$ be a probability measure on $\mathbb R^d$ and $\mu_N$ the empirical measure of $N\ge1$ i.i.d. samples from $\mu$. For all $n\ge0$ and $\ell\ge0$,
--   $$\sum_{F\in\mathcal P_\ell}\mathbb E\big|\mu_N(2^nF\cap B_n)-\mu(2^nF\cap B_n)\big|\le\min\Big\{2\mu(B_n),\,2^{d\ell/2}\big(\mu(B_n)/N\big)^{1/2}\Big\},$$
--   where $\mathcal P_\ell$ is the dyadic partition of $(-1,1]^d$ into $2^{d\ell}$ cubes, $2^nF=\{2^nx:x\in F\}$ and $B_n$ is the $n$-th dyadic shell.
--
--   It bounds the expected discrepancy of the empirical measure at one scale $\ell$ inside one shell $B_n$, and is the term-by-term estimate fed into Lemma 6.
--
--   **Formalization Note** Samples are points of $(\mathbb R^d)^N$ under $\mu^{\otimes N}$; expectations are lower Lebesgue integrals of $[0,\infty]$-valued functions.
-- source:
--   Fournier & Guillin, arXiv:1312.2128v1, Proof of Theorem 1, p. 8, second display

import Mathlib
import Definitions.Def_WassersteinLinOpt_Ball_wassersteinDist
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_FournierGuillin_Moment_Setting

open MeasureTheory
open scoped ENNReal

namespace FournierGuillin.Moment

/-- Proof of Theorem 1, p. 8, second display: for all `n ≥ 0`, `ℓ ≥ 0`,
`Σ_{F∈𝒫_ℓ} E|μ_N(2ⁿF ∩ B_n) − μ(2ⁿF ∩ B_n)| ≤ min{2μ(B_n), 2^{dℓ/2}(μ(B_n)/N)^{1/2}}`. -/
theorem level_bound {d : ℕ} (hd : 1 ≤ d) (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ] {N : ℕ} (hN : 1 ≤ N) (n ℓ : ℕ) :
    ∑ k : Fin d → Fin (2 ^ ℓ), ∫⁻ ω, ENNReal.ofReal
        |(WassersteinDRO.Duality.empiricalDistribution ω (scaledCell n ℓ k)).toReal
          - (μ (scaledCell n ℓ k)).toReal|
        ∂(Measure.pi fun _ : Fin N => μ)
      ≤ ENNReal.ofReal (min (2 * (μ (shell n)).toReal)
          (2 ^ ((d : ℝ) * ℓ / 2) * ((μ (shell n)).toReal / N) ^ (1 / 2 : ℝ))) := by sorry

end FournierGuillin.Moment
