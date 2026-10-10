-- Prove2me | Theorems.Thm_GraphLQGame_Asymptotics_eq_7_3
-- name    : GraphLQGame.Asymptotics.eq_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:26:23.034464+00:00
-- url     : https://prove2.me/theorems/6bbf792a-c1fe-4918-b119-351d696f4793
-- title:
--   (7.3) — Gaussian Poincaré bound $\mathrm{Var}(\int h\,dm^{G}(t))\le n^{-2}\sum_{j,k}|\Sigma_{jk}|$
-- statement:
--   Let $G$ be a finite transitive graph on $n$ vertices without isolated vertices, $T,\sigma,c>0$, $\boldsymbol X^G$ the equilibrium state process of Theorem 2.5 started from $\boldsymbol X^G(0) = 0$, and $t\in[0,T]$. Let $m^G(t) = \frac1n\sum_v\delta_{X^G_v(t)}$ be the empirical measure, $\Sigma$ the covariance matrix of $\boldsymbol X^G(t)$, and $h:\mathbb R\to\mathbb R$ bounded and $1$-Lipschitz. Then
--   $$\mathbb E\Big[\Big|\int h\,dm^G(t) - \mathbb E\int h\,dm^G(t)\Big|^2\Big]\le\frac1{n^2}\sum_{j,k=1}^n|\Sigma_{jk}|.$$
--
--   Combined with the correlation decay of Proposition 2.12 this shows that the empirical measure concentrates around its mean.
--
--   **Formalization Note** The left side is the variance of $\frac1n\sum_i h(X^G_i(t))$. The intermediate quantities $\operatorname{Var}(F(Z))\le\mathbb E|\nabla F(Z)|^2$ in the paper's display are proof devices and are not restated. Vertices are `Fin n`.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), §7.1.2, (7.3), p. 39

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_GraphLQGame_Equilibrium_Graph
import Definitions.Def_GraphLQGame_Equilibrium_Game
import Definitions.Def_GraphLQGame_Equilibrium_Equilibrium
import Definitions.Def_GraphLQGame_Asymptotics_Spectral
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace GraphLQGame.Asymptotics

open EthierKurtz

/-- **(7.3)** (Gaussian Poincaré bound), Lacker–Soret, arXiv:2005.14102v2, §7.1.2, p. 39.

Let `G` be a finite transitive graph on `n` vertices without isolated vertices, `X^G` the
equilibrium state process from `X^G(0) = 0`, `t ∈ [0, T]`, `m(t) = (1/n) Σ_v δ_{X_v(t)}` its
empirical measure, and `h` a bounded 1-Lipschitz function. Then
`E[|∫ h dm(t) − E ∫ h dm(t)|²] ≤ (1/n²) Σ_{j,k} |Σ_{jk}|`, where `Σ` is the covariance matrix of
`X^G(t)`.

Formalization Note: the left side is the variance of `(1/n) Σ_i h(X_i(t))`; the intermediate terms
`Var(F(Z)) ≤ E|∇F(Z)|²` of (7.3) are devices of the proof and are not restated. Vertices are
`Fin n`. -/
theorem eq_7_3 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {T σ c : ℝ}
    (hT : 0 < T) (hσ : 0 < σ) (hc : 0 < c) (htrans : GraphLQGame.Equilibrium.IsTransitive G) (hiso : GraphLQGame.Equilibrium.NoIsolated G)
    (f : ℝ → ℝ) (hf : GraphLQGame.Equilibrium.IsFSol c T (GraphLQGame.Equilibrium.QG G) f) (S : GraphLQGame.Equilibrium.StateSol n T σ 0 (GraphLQGame.Equilibrium.alphaG G c T f))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (h : ℝ →ᵇ ℝ) (hh : LipschitzWith 1 h) :
    variance (fun ω => (n : ℝ)⁻¹ * ∑ i, h (S.X t ω i)) S.P ≤
      ((n : ℝ)⁻¹) ^ 2 * ∑ j, ∑ k,
        |covariance (fun ω => S.X t ω j) (fun ω => S.X t ω k) S.P| := by sorry

end GraphLQGame.Asymptotics
