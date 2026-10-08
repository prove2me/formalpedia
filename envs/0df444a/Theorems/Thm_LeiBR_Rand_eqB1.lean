-- Prove2me | Theorems.Thm_LeiBR_Rand_eqB1
-- name    : LeiBR.Rand.eqB1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:08:46.630592+00:00
-- url     : https://prove2.me/theorems/5e560030-b7f7-46a0-b61c-e39346f79afe
-- title:
--   (B.1) — the exact randomized step contracts $\|\cdot\|_P^2$ by $\tilde a^2 = 1 - p_{\min}(1 - a^2)$
-- statement:
--   In the setting of (A.3) (Assumptions 1 and 2, $x_k$ an $\mathcal F_k$-measurable $X$-valued profile, coins $\chi_{i,k}$ with $\mathbb P(\chi_{i,k} = 1) = p_i$ independent of $\mathcal F_k$, and $t_{i,k} = x_{i,k} + \chi_{i,k}(\widehat x_i(x_k) - x_{i,k})$), almost surely
--   $$\mathbb E\big[\|t_k - x^*\|_P^2 \,\big|\, \mathcal F_k\big] \le \big(1 - p_{\min}(1 - a^2)\big)\,\|x_k - x^*\|_P^2 = \tilde a^2\,\|x_k - x^*\|_P^2,$$
--   where $p_{\min} = \min_i p_i$.
--
--   It turns (A.3) into a pure contraction in the weighted norm, with factor $\tilde a < 1$.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 32, App. B, (B.1)

import Mathlib
import Definitions.Def_LeiBR_Rand_Game
import Definitions.Def_LeiBR_Rand_ProxBR
import Definitions.Def_LeiBR_Rand_Assumption1
import Definitions.Def_LeiBR_Rand_SA
import Definitions.Def_LeiBR_Rand_Algorithm2
import Definitions.Def_LeiBR_Rand_Constants

open MeasureTheory ProbabilityTheory

namespace LeiBR.Rand

/-- (B.1), App. B, p. 32. In the setting of (A.3),
`E[‖t_k − x*‖²_P | F_k] ≤ (1 − p_min(1 − a²)) ‖x_k − x*‖²_P = ã² ‖x_k − x*‖²_P` a.s. -/
theorem eqB1 {N : ℕ} {n : Fin N → ℕ} {d : ℕ} (G : Game N n)
    (μξ : Measure (EuclideanSpace ℝ (Fin d)))
    (ψ : Fin N → LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i) (M : Fin N → ℝ)
    (hA1 : Assumption1 G μξ ψ gψ M) (mu : ℝ) (hmu : 0 < mu)
    (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n) (hxhat : IsProxBR G mu xhat)
    (hA2 : Assumption2 G mu) (xstar : LeiBR.Sync.Profile n) (hNE : G.IsNE xstar)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ mΩ) (k : ℕ) (p : Fin N → ℝ) (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i ≤ 1)
    (xk : Ω → LeiBR.Sync.Profile n) (hxk_meas : StronglyMeasurable[F k] xk)
    (hxk_feas : ∀ ω, G.Feasible (xk ω))
    (χ : Fin N → Ω → ℕ) (hχ1 : ∀ i ω, χ i ω ≤ 1) (hχ_meas : ∀ i, Measurable (χ i))
    (hχ_prob : ∀ i, P {ω | χ i ω = 1} = ENNReal.ofReal (p i))
    (hχ_indep : ∀ i, Indep (MeasurableSpace.comap (χ i) inferInstance) (F k) P) :
    P[fun ω => wnorm p ((fun i => xk ω i + (χ i ω : ℝ) • (xhat (xk ω) i - xk ω i)) - xstar) ^ 2 | F k]
      ≤ᵐ[P] fun ω => (1 - pmin p * (1 - contrFactor G mu ^ 2)) * wnorm p (xk ω - xstar) ^ 2 := by sorry

end LeiBR.Rand
