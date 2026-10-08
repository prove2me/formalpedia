-- Prove2me | Theorems.Thm_LeiBR_Rand_eqA3
-- name    : LeiBR.Rand.eqA3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:09:45.513053+00:00
-- url     : https://prove2.me/theorems/8822e825-ef2c-445a-955e-3cb1442e1610
-- title:
--   (A.3) — one exact randomized BR step contracts $\|x_k - x^*\|_P^2$ in conditional mean
-- statement:
--   Let Assumptions 1 and 2 hold, $\mu > 0$, $a = \|\Gamma\|$, and let $x^*$ be a Nash equilibrium. Let $x_k$ be an $\mathcal F_k$-measurable random profile with values in $X$. Let $\chi_{i,k} \in \{0,1\}$ be coins with $\mathbb P(\chi_{i,k} = 1) = p_i \in (0,1]$, each independent of $\mathcal F_k$. Define the exact randomized step
--   $$t_{i,k} = x_{i,k} + \chi_{i,k}\big(\widehat x_i(x_k) - x_{i,k}\big).$$
--   Then, almost surely,
--   $$\mathbb E\big[\|t_k - x^*\|_P^2 \,\big|\, \mathcal F_k\big] \le \|x_k - x^*\|_P^2 - (1 - a^2)\,\|x_k - x^*\|^2,$$
--   where $\|\cdot\|_P$ is the weighted norm (A.2) and $\|x_k - x^*\|^2 = \sum_i \|x_{i,k} - x_i^*\|^2$.
--
--   This is the one-step descent inequality of the randomized scheme for the exact best response, the starting point of both Lemma 4 and Lemma 5.
--
--   **Formalization Note** Only the final inequality of the paper's display (A.3) is stated; its intermediate equalities, which use (A.1), are not.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 31, App. A, (A.1)–(A.3)

import Mathlib
import Definitions.Def_LeiBR_Rand_Game
import Definitions.Def_LeiBR_Rand_ProxBR
import Definitions.Def_LeiBR_Rand_Assumption1
import Definitions.Def_LeiBR_Rand_SA
import Definitions.Def_LeiBR_Rand_Algorithm2
import Definitions.Def_LeiBR_Rand_Constants

open MeasureTheory ProbabilityTheory

namespace LeiBR.Rand

/-- (A.3), App. A, p. 31. Let `x_k` be an `F_k`-measurable `X`-valued random profile and let the
coins `χ_i ∈ {0,1}` satisfy `P(χ_i = 1) = p_i` and be independent of `F_k`. With
`t_{i,k} = x_{i,k} + χ_{i,k}(x̂_i(x_k) − x_{i,k})`,
`E[‖t_k − x*‖²_P | F_k] ≤ ‖x_k − x*‖²_P − (1 − a²)‖x_k − x*‖²` a.s. -/
theorem eqA3 {N : ℕ} {n : Fin N → ℕ} {d : ℕ} (G : Game N n)
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
      ≤ᵐ[P] fun ω => wnorm p (xk ω - xstar) ^ 2
        - (1 - contrFactor G mu ^ 2) * blockNorm (xk ω - xstar) ^ 2 := by sorry

end LeiBR.Rand
