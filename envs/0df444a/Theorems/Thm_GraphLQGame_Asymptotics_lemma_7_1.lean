-- Prove2me | Theorems.Thm_GraphLQGame_Asymptotics_lemma_7_1
-- name    : GraphLQGame.Asymptotics.lemma_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:26:08.96222+00:00
-- url     : https://prove2.me/theorems/d596f233-ad6a-43f2-994e-9624e1a47275
-- title:
--   Lemma 7.1 — $\mu_{G_n}\to\delta_{-1}$ iff $\delta(G_n)\to\infty$; a limit $\mu\ne\delta_{-1}$ forces bounded degrees
-- statement:
--   Let $(G_n)$ be a sequence of finite transitive graphs without isolated vertices, and let $\delta(G_n)$ be the common degree of the vertices of $G_n$. Then
--
--   1. $\mu_{G_n}\to\delta_{-1}$ weakly if and only if $\delta(G_n)\to\infty$;
--   2. if $\mu_{G_n}\to\mu$ weakly for a probability measure $\mu\ne\delta_{-1}$, then $\sup_n\delta(G_n)<\infty$.
--
--   The lemma separates the dense regime (degrees diverge, spectral limit $\delta_{-1}$, the mean-field case) from the sparse one (bounded degrees). The proof of Theorem 2.6(3) uses it to bound the size of graph balls in the sparse case.
--
--   **Formalization Note** $\delta(G_n)$ is Mathlib's minimum degree, which for a transitive graph is the degree of every vertex (and $0$ for a graph with no vertex). Weak convergence is tested against all bounded continuous functions on $\mathbb R$.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), §7.1.2, Lemma 7.1, p. 38

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

/-- **Lemma 7.1**, Lacker–Soret, arXiv:2005.14102v2, §7.1.2, p. 38.

Let `G k` be finite transitive graphs without isolated vertices, with common degree `δ(G_k)`.
Then `μ_{G_k} → δ_{−1}` weakly if and only if `δ(G_k) → ∞`; and if `μ_{G_k} → μ` weakly for a
probability measure `μ ≠ δ_{−1}`, then `sup_k δ(G_k) < ∞`.

Formalization Note: `δ(G_k)` is `(G k).minDegree`, which for a transitive graph is the degree of
every vertex (and `0` for a graph with no vertex). Weak convergence is tested against all bounded
continuous `h : ℝ → ℝ`. -/
theorem lemma_7_1 {N : ℕ → ℕ} (G : ∀ k, SimpleGraph (Fin (N k))) [∀ k, DecidableRel (G k).Adj]
    (htrans : ∀ k, GraphLQGame.Equilibrium.IsTransitive (G k)) (hiso : ∀ k, GraphLQGame.Equilibrium.NoIsolated (G k)) :
    (WeakTendsto (fun k => GraphLQGame.Equilibrium.specMeasure (G k)) (Measure.dirac (-1)) ↔
        Tendsto (fun k => (G k).minDegree) atTop atTop) ∧
      ∀ μ : Measure ℝ, IsProbabilityMeasure μ → μ ≠ Measure.dirac (-1) →
        WeakTendsto (fun k => GraphLQGame.Equilibrium.specMeasure (G k)) μ →
          BddAbove (Set.range fun k => (G k).minDegree) := by sorry

end GraphLQGame.Asymptotics
