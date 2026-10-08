-- Prove2me | Theorems.Thm_LeiBR_Async_lemma_8
-- name    : LeiBR.Async.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:07:22.696196+00:00
-- url     : https://prove2.me/theorems/e3393ffd-432b-48fb-9eca-c47dea9445d7
-- title:
--   Lemma 8 — the SA inner loop (43) reaches conditional mean-square error $Q_i/(t+1)$
-- statement:
--   Let Assumption 1(a)–(b) hold and $\mu > 0$, let $\hat x$ be the proximal best-response map, and let $\Pi_{X_i}$ be the Euclidean projection onto $X_i$. Fix a player $i$ and a major iteration $k$, and let $\mathcal F_k$ be a sub-$\sigma$-algebra. Let $y = y^i_k : \Omega \to X$ be an $\mathcal F_k$-measurable outdated profile, and run (43) from $z_{i,1} = y_i = x_{i,k}$ with samples $\xi^t$, where $\xi^t$ is measurable for $\mathcal G_{t+1}$, the $\sigma$-algebras $\mathcal G_t$ increase with $t$ and $\mathcal G_1 \supseteq \mathcal F_k$ (they play the role of $\sigma\{\mathcal F_k, \xi^{[t-1]}_{i,k}\}$), and the sampled-gradient map is jointly measurable. Assume that for $t = 1,\dots,j$ the sampled gradient $g_t = \nabla_{x_i}\psi_i(z_{i,t}, y_{-i};\xi^t)$ satisfies
--   $$\mathbb E\big[g_t \,\big|\, \mathcal G_t\big] = \nabla_{x_i} f_i(z_{i,t}, y_{-i}),\qquad \mathbb E\big[\|g_t\|^2 \,\big|\, \mathcal G_t\big] \le M_i^2\qquad\text{a.s.}$$
--   (with $\|g_t\|^2$ integrable). Then for $t = 1,\dots,j$,
--   $$\mathbb E\big[\|z_{i,t} - \hat x_i(y^i_k)\|^2 \,\big|\, \mathcal F_k\big] \le \frac{Q_i}{t+1}\quad\text{a.s.},\qquad Q_i = \frac{2M_i^2}{\mu^2} + 2D_{X_i}^2 .$$
--
--   This is the error bound for the stochastic-approximation solver of each proximal best-response subproblem; it tells how many gradient steps achieve the accuracy (38).
--
--   **Formalization Note** Statement repair: the page writes $\psi_i$ for $\nabla_{x_i}\psi_i$ in both hypotheses, and its second hypothesis "$\mathbb E[\|\nabla_{x_i}\psi_i\|^2 \mid \cdot] = \|\nabla_{x_i}f_i\|^2$" forces zero noise; the proof uses only the bound $\le M_i^2$, which is assumed instead (it follows from the literal hypothesis and Assumption 1(d)). The lemma is stated for a single solver call with a general $\mathcal F_k$-measurable starting profile; the $\sigma$-algebras $\mathcal G_t$ are parameters satisfying the relations above.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 19, Lemma 8 (with (43), p. 18; Q_i from Lemma 3, p. 10)

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_LeiBR_Async_Game
import Definitions.Def_LeiBR_Async_Model
import Definitions.Def_LeiBR_Async_Algorithm

namespace LeiBR.Async

open MeasureTheory

/-- Lemma 8 (§5.3, p. 19), error of the stochastic approximation inner loop (43). In major iteration
`k`, let player `i` start (43) from its own coordinate of the `F_k`-measurable outdated profile
`y = y^i_k ∈ X` (so `z_1 = y_i = x_{i,k}`), with samples `ξ^t` measurable for `G_{t+1}`, where
`G_t ⊇ F_k` plays the role of `σ{F_k, ξ^{[t−1]}_{i,k}}`. If for `t = 1, …, j` the sampled gradients are
conditionally unbiased with conditional second moment at most `M_i²` (`IsSAOracle`), then for
`t = 1, …, j`, `E[‖z_t − x̂_i(y)‖² | F_k] ≤ Q_i/(t + 1)` a.s., with `Q_i = 2M_i²/μ² + 2D²_{X_i}`. -/
theorem lemma_8 {Ω : Type*} (Fk : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N d : ℕ} {n : Fin N → ℕ} (X : ∀ i, Set (LeiBR.Sync.Strat n i)) (f : Fin N → LeiBR.Sync.Profile n → ℝ)
    (hA1 : Assumption1ab X f) (μ : ℝ) (hμ : 0 < μ) (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n)
    (hxhat : LeiBR.Sync.IsProxBR X f μ xhat) (M : Fin N → ℝ)
    (gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i)
    (hgψ : ∀ i, Measurable (Function.uncurry (gψ i)))
    (proj : ∀ i, LeiBR.Sync.Strat n i → LeiBR.Sync.Strat n i)
    (hproj : ∀ i, SpectralProjGrad.Shared.IsProjOnto (X i) (proj i))
    (i : Fin N) (hFk : Fk ≤ mΩ) (G : ℕ → MeasurableSpace Ω)
    (hG : ∀ t, G t ≤ mΩ) (hFG : Fk ≤ G 1) (hGmono : ∀ t, G t ≤ G (t + 1))
    (y : Ω → LeiBR.Sync.Profile n) (hy : Measurable[Fk] y) (hyX : ∀ ω, y ω ∈ profileSet X)
    (ξ : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hξ : ∀ t, Measurable[G (t + 1)] (ξ t)) (j : ℕ)
    (horacle : IsSAOracle P f gψ proj μ M i y ξ G j) :
    ∀ t, 1 ≤ t → t ≤ j →
      P[fun ω => ‖saPath proj gψ μ i (y ω) (fun s => ξ s ω) t - xhat (y ω) i‖ ^ 2 | Fk]
        ≤ᵐ[P] fun _ => LeiBR.Sync.Qconst X M μ i / ((t : ℝ) + 1) := by sorry

end LeiBR.Async
