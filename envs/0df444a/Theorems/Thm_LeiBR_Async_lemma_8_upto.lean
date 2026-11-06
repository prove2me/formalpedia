-- Prove2me | Theorems.Thm_LeiBR_Async_lemma_8_upto
-- name    : LeiBR.Async.lemma_8_upto
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-05T10:53:12.045032+00:00
-- url     : https://prove2.me/theorems/435fd57a-2022-4de8-919d-4b9ede814db9
-- title:
--   Lemma 8 (horizon-restricted measurability) — the SA inner loop (43) reaches conditional mean-square error $Q_i/(t+1)$
-- statement:
--   Let Assumption 1(a)–(b) hold and $\mu > 0$, let $\hat x$ be the proximal best-response map, and let $\Pi_{X_i}$ be the Euclidean projection onto $X_i$. Fix a player $i$, a major iteration $k$, a horizon $j \in \mathbb N$, and a sub-$\sigma$-algebra $\mathcal F_k$. Let $y = y^i_k : \Omega \to X$ be an $\mathcal F_k$-measurable outdated profile, and run (43) from $z_{i,1} = y_i = x_{i,k}$ with samples $\xi^t$. The $\sigma$-algebras $\mathcal G_t$ increase with $t$, satisfy $\mathcal G_1 \supseteq \mathcal F_k$ (they play the role of $\sigma\{\mathcal F_k, \xi^{[t-1]}_{i,k}\}$), and are sub-$\sigma$-algebras of the ambient one **for $t \le j$**; the samples $\xi^t$ that enter the iterates $z_{i,2},\dots,z_{i,j}$, i.e. those with **$t < j$**, are $\mathcal G_{t+1}$-measurable; and the sampled-gradient map is jointly measurable. Assume that for $t = 1,\dots,j$ the sampled gradient $g_t = \nabla_{x_i}\psi_i(z_{i,t}, y_{-i};\xi^t)$ satisfies
--   $$\mathbb E\big[g_t \,\big|\, \mathcal G_t\big] = \nabla_{x_i} f_i(z_{i,t}, y_{-i}),\qquad \mathbb E\big[\|g_t\|^2 \,\big|\, \mathcal G_t\big] \le M_i^2\qquad\text{a.s.}$$
--   (with $\|g_t\|^2$ integrable). Then for $t = 1,\dots,j$,
--   $$\mathbb E\big[\|z_{i,t} - \hat x_i(y^i_k)\|^2 \,\big|\, \mathcal F_k\big] \le \frac{Q_i}{t+1}\quad\text{a.s.},\qquad Q_i = \frac{2M_i^2}{\mu^2} + 2D_{X_i}^2 .$$
--
--   This is Lemma 8 with the measurability requirements restricted to the indices the iterates $z_{i,1},\dots,z_{i,j}$ actually use. It is the form needed in the proof of Theorem 3, whose hypotheses only guarantee $\mathcal G_{i,k,t} \subseteq \mathcal F_{k+1}$ for $t \le j_{i,k}$; and it implies `LeiBR.Async.lemma_8` directly.
--
--   **Formalization Note** Same repairs as `LeiBR.Async.lemma_8`: the page writes $\psi_i$ for $\nabla_{x_i}\psi_i$, and its literal second-moment hypothesis (an equality with $\|\nabla_{x_i} f_i\|^2$) is replaced by the bound $\le M_i^2$ that the proof uses. Compared with `lemma_8`, the hypotheses $\mathcal G_t \le \mathcal M$ (ambient $\sigma$-algebra) are assumed only for $t \le j$, and the measurability of $\xi^t$ only for $t < j$ (the last sample $\xi^j$ only feeds $z_{i,j+1}$).
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 19, Lemma 8 (with (43), p. 18; Q_i from Lemma 3, p. 10), as used in the proof of Theorem 3, p. 19

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_LeiBR_Async_Game
import Definitions.Def_LeiBR_Async_Model
import Definitions.Def_LeiBR_Async_Algorithm

namespace LeiBR.Async

open MeasureTheory

/-- Lemma 8 (§5.3, p. 19), error of the stochastic approximation inner loop (43), with the
measurability hypotheses required only up to the horizon `j`. In major iteration `k`, player `i`
starts (43) from its own coordinate of the `F_k`-measurable outdated profile `y = y^i_k ∈ X`
(so `z_1 = y_i = x_{i,k}`). The σ-algebras `G_t ⊇ F_k` play the role of `σ{F_k, ξ^{[t−1]}_{i,k}}`; they
are sub-σ-algebras of the ambient one for `t ≤ j`, and the samples `ξ^t` used by the iterates
`z_2, …, z_j` (that is, `t < j`) are `G_{t+1}`-measurable. If for `t = 1, …, j` the sampled gradients
are conditionally unbiased with conditional second moment at most `M_i²` (`IsSAOracle`), then for
`t = 1, …, j`, `E[‖z_t − x̂_i(y)‖² | F_k] ≤ Q_i/(t + 1)` a.s., with `Q_i = 2M_i²/μ² + 2D²_{X_i}`.

Formalization Note: identical to `LeiBR.Async.lemma_8` except that `G t ≤ mΩ` is assumed only for
`t ≤ j` and `ξ t` is assumed `G (t+1)`-measurable only for `t < j` (the last sample `ξ^j` only feeds
`z_{j+1}`); this is the form in which Theorem 3's hypotheses supply the inner-loop σ-algebras. -/
theorem lemma_8_upto {Ω : Type*} (Fk : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N d : ℕ} {n : Fin N → ℕ} (X : ∀ i, Set (LeiBR.Sync.Strat n i)) (f : Fin N → LeiBR.Sync.Profile n → ℝ)
    (hA1 : Assumption1ab X f) (μ : ℝ) (hμ : 0 < μ) (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n)
    (hxhat : LeiBR.Sync.IsProxBR X f μ xhat) (M : Fin N → ℝ)
    (gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i)
    (hgψ : ∀ i, Measurable (Function.uncurry (gψ i)))
    (proj : ∀ i, LeiBR.Sync.Strat n i → LeiBR.Sync.Strat n i)
    (hproj : ∀ i, SpectralProjGrad.Shared.IsProjOnto (X i) (proj i))
    (i : Fin N) (j : ℕ) (hFk : Fk ≤ mΩ) (G : ℕ → MeasurableSpace Ω)
    (hG : ∀ t, t ≤ j → G t ≤ mΩ) (hFG : Fk ≤ G 1) (hGmono : ∀ t, G t ≤ G (t + 1))
    (y : Ω → LeiBR.Sync.Profile n) (hy : Measurable[Fk] y) (hyX : ∀ ω, y ω ∈ profileSet X)
    (ξ : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hξ : ∀ t, t < j → Measurable[G (t + 1)] (ξ t))
    (horacle : IsSAOracle P f gψ proj μ M i y ξ G j) :
    ∀ t, 1 ≤ t → t ≤ j →
      P[fun ω => ‖saPath proj gψ μ i (y ω) (fun s => ξ s ω) t - xhat (y ω) i‖ ^ 2 | Fk]
        ≤ᵐ[P] fun _ => LeiBR.Sync.Qconst X M μ i / ((t : ℝ) + 1) := by sorry

end LeiBR.Async
