-- Prove2me | Theorems.Thm_GraphLQGame_Asymptotics_eq_2_9
-- name    : GraphLQGame.Asymptotics.eq_2_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:26:17.215991+00:00
-- url     : https://prove2.me/theorems/ada5ec66-33dc-45aa-acf0-1a6e04fa0487
-- title:
--   (2.9) — $\mathrm{Val}(G) = -\frac{\sigma^2}{2}\log\frac{\mathrm{Tr}(P_G(0))}{nf_G'(T)} = -\frac{\sigma^2}{2}\log\int\frac{-\lambda}{1-f_G(T)\lambda}\mu_G(d\lambda)$
-- statement:
--   Let $G$ be a finite transitive graph on $n$ vertices without isolated vertices, $T,\sigma,c>0$, $f_G$ the solution of the ODE of Theorem 2.5 and $\boldsymbol X^G$ the equilibrium state process started from $\boldsymbol X^G(0)=0$. Then every player's equilibrium cost $J^G_v$ is finite, and the average value $\mathrm{Val}(G) = \frac1n\sum_v J^G_v$ satisfies
--   $$\mathrm{Val}(G) = -\frac{\sigma^2}{2}\log\frac{\operatorname{Tr}(P_G(0))}{n f_G'(T)} = -\frac{\sigma^2}{2}\log\int_{[-2,0]}\frac{-\lambda}{1 - f_G(T)\lambda}\,\mu_G(d\lambda).$$
--
--   This expresses the value through the spectral measure $\mu_G$, so that its large-graph limit (Theorem 2.6(4)) follows from weak convergence of $\mu_{G_n}$ and convergence of $f_{G_n}(T)$.
--
--   **Formalization Note** Costs are $[0,\infty]$-valued and are converted to real numbers after their finiteness is asserted. $f_G'(T)$ is written as its ODE value $c\,Q_G'(f_G(T))$. Vertices are `Fin n`.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), §2.3, (2.9), p. 7; (2.6), p. 6

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

/-- **(2.9)**, Lacker–Soret, arXiv:2005.14102v2, §2.3, p. 7.

Let `G` be a finite transitive graph on `n` vertices without isolated vertices and `X^G` the
equilibrium state process from `X^G(0) = 0`. Then every player's GraphLQGame.Equilibrium.cost is finite and
`Val(G) = (1/n) Σ_v J_v^G = −(σ²/2) log (Tr P_G(0) / (n f'_G(T)))
        = −(σ²/2) log ∫_{[−2,0]} −λ / (1 − f_G(T)λ) μ_G(dλ)`.

Formalization Note: costs are `ℝ≥0∞` lower integrals, converted to reals after finiteness;
`f'_G(T)` is written as its ODE value `c Q'_G(f_G(T))`, as in `P_G`. Vertices are `Fin n`. -/
theorem eq_2_9 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {T σ c : ℝ}
    (hT : 0 < T) (hσ : 0 < σ) (hc : 0 < c) (htrans : GraphLQGame.Equilibrium.IsTransitive G) (hiso : GraphLQGame.Equilibrium.NoIsolated G)
    (f : ℝ → ℝ) (hf : GraphLQGame.Equilibrium.IsFSol c T (GraphLQGame.Equilibrium.QG G) f) (S : GraphLQGame.Equilibrium.StateSol n T σ 0 (GraphLQGame.Equilibrium.alphaG G c T f)) :
    (∀ v, GraphLQGame.Equilibrium.cost G c T S v ≠ ⊤) ∧
      (n : ℝ)⁻¹ * ∑ v, (GraphLQGame.Equilibrium.cost G c T S v).toReal =
        -(σ ^ 2 / 2) * Real.log ((GraphLQGame.Equilibrium.PG G c T f 0).trace / (n * (c * deriv (GraphLQGame.Equilibrium.QG G) (f T)))) ∧
      -(σ ^ 2 / 2) * Real.log ((GraphLQGame.Equilibrium.PG G c T f 0).trace / (n * (c * deriv (GraphLQGame.Equilibrium.QG G) (f T)))) =
        -(σ ^ 2 / 2) * Real.log (∫ l in Set.Icc (-2 : ℝ) 0, -l / (1 - f T * l) ∂(GraphLQGame.Equilibrium.specMeasure G)) := by sorry

end GraphLQGame.Asymptotics
