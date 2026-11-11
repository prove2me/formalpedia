-- Prove2me | Theorems.Thm_OptimalLCA_Matching_theorem_5_1
-- name    : OptimalLCA.Matching.theorem_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:47:57.232032+00:00
-- url     : https://prove2.me/theorems/eba1d547-fd92-4aab-a67b-2f831b0621b7
-- title:
--   Theorem 5.1 — 0 ≤ 2ν_f(G) − P(q̂) ≤ 3B_Δν_f(G)/T; T = ⌈3B_Δ/δ⌉ gives P(q̂) ≥ (2 − δ)ν_f(G)
-- statement:
--   Let $G$ have maximum degree at most $\Delta\ge2$ and let $\hat q$ be the output of Algorithm 2 after $T\ge1$ rounds. With $B_\Delta=200+400\log(2\Delta)$,
--   $$0\le2\nu_f(G)-P(\hat q)\le\frac{3B_\Delta\,\nu_f(G)}{T}.$$
--   Consequently, for every $\delta>0$, $T=\lceil3B_\Delta/\delta\rceil$ gives $P(\hat q)\ge(2-\delta)\nu_f(G)$.
--
--   Differences from the source:
--   - encoding: the optimizer runs only on nonisolated vertices; isolated vertices output their dummy → Algorithm 2 run on all vertices; an isolated vertex's block is its dummy alone, so its distributions stay on the dummy, and its price never enters a proposal update; reason: the outputs q̂ coincide
--   - encoding: a graph with vertex set [n] → any finite vertex type V with a SimpleGraph (decidable adjacency); reason: relabelling; every graph on [n] is an instance
-- source:
--   Cohen, Roghani, Optimal LCA and Sublinear Estimation for Bipartite Matching in Δ^O(1/ε) Queries, arXiv:2611.06024 (version not printed; PDF sha256 5a43ec12…3eb3), p. 24, Theorem 5.1

import Mathlib
import Definitions.Def_OptimalLCA_Matching_Graph
import Definitions.Def_OptimalLCA_Matching_SaddlePoint
import Definitions.Def_OptimalLCA_Matching_Optimizer

namespace OptimalLCA.Matching

/-- Theorem 5.1 (convergence rate). Let `G` have maximum degree at most `Δ` and let `q̂` be
the output of Algorithm 2 after `T` rounds. With `B_Δ = 200 + 400 log(2Δ)`,
`0 ≤ 2 ν_f(G) - P(q̂) ≤ 3 B_Δ ν_f(G) / T`. Consequently `T = ⌈3 B_Δ / δ⌉` gives
`P(q̂) ≥ (2 - δ) ν_f(G)`. -/
theorem theorem_5_1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (Δ : ℕ) (hΔ : 2 ≤ Δ) (hdeg : ∀ v, G.degree v ≤ Δ) :
    (∀ T : ℕ, 1 ≤ T →
      0 ≤ 2 * fracMatchingNumber G - acceptedMass G (qHat G Δ T) ∧
      2 * fracMatchingNumber G - acceptedMass G (qHat G Δ T) ≤
        3 * bDelta Δ * fracMatchingNumber G / (T : ℝ)) ∧
    ∀ δ : ℝ, 0 < δ →
      (2 - δ) * fracMatchingNumber G ≤ acceptedMass G (qHat G Δ ⌈3 * bDelta Δ / δ⌉₊) := by sorry

end OptimalLCA.Matching
