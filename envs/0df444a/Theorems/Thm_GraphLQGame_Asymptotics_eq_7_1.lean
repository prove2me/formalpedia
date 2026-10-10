-- Prove2me | Theorems.Thm_GraphLQGame_Asymptotics_eq_7_1
-- name    : GraphLQGame.Asymptotics.eq_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:28:13.075188+00:00
-- url     : https://prove2.me/theorems/b610831f-6555-4ced-b1ef-33fe3bb5f608
-- title:
--   (7.1) — $\mathbb E|\int h\,dm^{G_n}(t)-\mathbb E\int h\,dm^{G_n}(t)|^2\to0$ for bounded 1-Lipschitz $h$
-- statement:
--   Assume the setting of Theorem 2.6: $(G_n)$ finite transitive graphs without isolated vertices, $|G_n|\to\infty$, $\mu_{G_n}\to\mu$ weakly for a probability measure $\mu$, $T,\sigma,c>0$, and $\boldsymbol X^{G_n}$ the equilibrium state processes of Theorem 2.5 started from $\boldsymbol X^{G_n}(0) = 0$. Let $m^{G_n}(t) = \frac1{|G_n|}\sum_{v\in G_n}\delta_{X^{G_n}_v(t)}$. Then for every $t\in[0,T]$ and every bounded $1$-Lipschitz $h$,
--   $$\lim_{n\to\infty}\mathbb E\Big[\Big|\int h\,dm^{G_n}(t) - \mathbb E\int h\,dm^{G_n}(t)\Big|^2\Big] = 0.$$
--
--   Together with Theorem 2.6(2) this yields the convergence of the empirical measure in Theorem 2.6(3).
--
--   **Formalization Note** The expectation is the variance of $\frac1{|G_n|}\sum_i h(X^{G_n}_i(t))$. Each state process is any solution of (2.1) under $\alpha^{G_n}$, on its own probability space.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), §7.1.2, (7.1), p. 38

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

/-- **(7.1)** (Concentration of the empirical measure), Lacker–Soret, arXiv:2005.14102v2, §7.1.2,
p. 38.

Under the hypotheses of Theorem 2.6 (transitive graphs `G k` without isolated vertices, `N k → ∞`,
`μ_{G_k} → μ` weakly, `X^{G_k}(0) = 0`), for every `t ∈ [0, T]` and every bounded 1-Lipschitz `h`,
`lim_k E[|∫ h dm^{G_k}(t) − E ∫ h dm^{G_k}(t)|²] = 0`, where `m^{G_k}(t)` is the empirical measure
of `X^{G_k}(t)`.

Formalization Note: the expectation of the squared deviation is the variance of
`(1/N_k) Σ_i h(X_i(t))`; the state processes are any solutions of (2.1) under `α^{G_k}`, each on its
own probability space. -/
theorem eq_7_1 {N : ℕ → ℕ} (G : ∀ k, SimpleGraph (Fin (N k)))
    [∀ k, DecidableRel (G k).Adj] {T σ c : ℝ} (hT : 0 < T) (hσ : 0 < σ) (hc : 0 < c)
    (htrans : ∀ k, GraphLQGame.Equilibrium.IsTransitive (G k)) (hiso : ∀ k, GraphLQGame.Equilibrium.NoIsolated (G k))
    (hN : Tendsto N atTop atTop) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hconv : WeakTendsto (fun k => GraphLQGame.Equilibrium.specMeasure (G k)) μ)
    (fk : ℕ → ℝ → ℝ) (hfk : ∀ k, GraphLQGame.Equilibrium.IsFSol c T (GraphLQGame.Equilibrium.QG (G k)) (fk k))
    (S : ∀ k, GraphLQGame.Equilibrium.StateSol (N k) T σ 0 (GraphLQGame.Equilibrium.alphaG (G k) c T (fk k)))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (h : ℝ →ᵇ ℝ) (hh : LipschitzWith 1 h) :
    Tendsto (fun k => variance (fun ω => (N k : ℝ)⁻¹ * ∑ i, h ((S k).X t ω i)) (S k).P)
      atTop (𝓝 0) := by sorry

end GraphLQGame.Asymptotics
