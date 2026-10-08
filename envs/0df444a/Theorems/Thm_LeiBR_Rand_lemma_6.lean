-- Prove2me | Theorems.Thm_LeiBR_Rand_lemma_6
-- name    : LeiBR.Rand.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:08:51.578164+00:00
-- url     : https://prove2.me/theorems/3ddbc545-638c-4519-aa01-2eefeb8e90c2
-- title:
--   Lemma 6 — the SA scheme reaches $\mathbb E[\|z_{i,t} - \widehat x_i(y_k)\|^2 \mid \mathcal F_k] \le Q_i/(t+1)$
-- statement:
--   Let Assumption 1 hold and $\mu > 0$. Let $y_k$ be an $\mathcal F_k$-measurable random profile with values in $X$. Let player $i$'s samples $\xi^t_{i,k}$, $t \ge 1$, be i.i.d. with the law of $\xi$, and let the vector $\xi_{i,k} = (\xi^1_{i,k}, \xi^2_{i,k}, \dots)$ be independent of $\mathcal F_k$. Run the projected stochastic gradient scheme (SA$_{i,k}$) from $z_{i,1} = y_{i,k}$, with $\gamma_t = 1/(\mu(t+1))$. Then for every $t \ge 1$,
--   $$\mathbb E\big[\|z_{i,t} - \widehat x_i(y_k)\|^2 \,\big|\, \mathcal F_k\big] \le \frac{Q_i}{t+1} \quad \text{a.s.},$$
--   with $Q_i = 2M_i^2/\mu^2 + 2D_{X_i}^2$.
--
--   It is the inner-loop guarantee: $j$ steps of (SA$_{i,k}$) produce an inexact best response of accuracy $Q_i/j$ in conditional mean square, which is how the inexactness condition (33) is met.
--
--   **Formalization Note**
--   - The paper states the lemma for $i \in I_k$, the players with $\chi_{i,k} = 1$. Lean states it for any player, since the samples are drawn regardless of the coin.
--   - In Algorithm 2, $z_{i,1} = x_{i,k}$ and $y_k = x_k$.
--   - $\Pi_{X_i}$ is any map satisfying `SpectralProjGrad.Shared.IsProjOnto`.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 15, Lemma 6 (cf. Lemma 3, p. 10)

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_LeiBR_Rand_Game
import Definitions.Def_LeiBR_Rand_ProxBR
import Definitions.Def_LeiBR_Rand_Assumption1
import Definitions.Def_LeiBR_Rand_SA
import Definitions.Def_LeiBR_Rand_Algorithm2
import Definitions.Def_LeiBR_Rand_Constants

open MeasureTheory ProbabilityTheory

namespace LeiBR.Rand

/-- Lemma 6, p. 15. Let `y_k` be an `F_k`-measurable `X`-valued random profile and let player `i`'s
samples `ξ^t` (`t ≥ 1`) be i.i.d. with the law `μξ` of `ξ` and, as a vector, independent of `F_k`.
Run (SA_{i,k}) from `z_{i,1} = y_{i,k}`. Then for every `t ≥ 1`,
`E[‖z_{i,t} − x̂_i(y_k)‖² | F_k] ≤ Q_i/(t+1)` a.s. -/
theorem lemma_6 {N : ℕ} {n : Fin N → ℕ} {d : ℕ} (G : Game N n)
    (μξ : Measure (EuclideanSpace ℝ (Fin d)))
    (ψ : Fin N → LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i) (M : Fin N → ℝ)
    (hA1 : Assumption1 G μξ ψ gψ M) (mu : ℝ) (hmu : 0 < mu)
    (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n) (hxhat : IsProxBR G mu xhat)
    (proj : ∀ i, LeiBR.Sync.Strat n i → LeiBR.Sync.Strat n i)
    (hproj : ∀ i, SpectralProjGrad.Shared.IsProjOnto (G.X i) (proj i))
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ mΩ) (k : ℕ)
    (y : Ω → LeiBR.Sync.Profile n) (hy_meas : StronglyMeasurable[F k] y) (hy_feas : ∀ ω, G.Feasible (y ω))
    (s : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hs_meas : ∀ t, Measurable (s t))
    (hs_law : ∀ t, Measure.map (s (t + 1)) P = μξ) (hs_iid : iIndepFun (fun t => s (t + 1)) P)
    (hs_indep : Indep (⨆ t, MeasurableSpace.comap (s (t + 1)) inferInstance) (F k) P)
    (i : Fin N) (t : ℕ) (ht : 1 ≤ t) :
    P[fun ω => ‖saIter (proj i) (fun t' z => saDir gψ mu i (y ω) (s t' ω) z) mu (y ω i) t
        - xhat (y ω) i‖ ^ 2 | F k] ≤ᵐ[P] fun _ => Qconst G M mu i / ((t : ℝ) + 1) := by sorry

end LeiBR.Rand
