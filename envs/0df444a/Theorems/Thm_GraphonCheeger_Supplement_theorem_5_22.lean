-- Prove2me | Theorems.Thm_GraphonCheeger_Supplement_theorem_5_22
-- name    : GraphonCheeger.Supplement.theorem_5_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:36:37.859971+00:00
-- url     : https://prove2.me/theorems/c2fe7f40-37e2-4e9c-9f97-dc468b077b3c
-- title:
--   Theorem 5.22 — $q^*_{\mathrm{frac}}(G)=\lim_b q^*(G[b])=\sup_b q^*(G[b])$
-- statement:
--   For any graph $G$, with $G[b]$ its $b$-blow-up,
--   $$
--   q^*_{\mathrm{frac}}(G)=\lim_{b\to\infty}q^*(G[b])=\sup_{b\ge1}q^*(G[b]),
--   $$
--   and furthermore $q^*_{\mathrm{frac}}(G[b])=q^*_{\mathrm{frac}}(G)$ for every $b\ge1$.
--
--   Fractional modularity is thus the limit of the modularity of blow-ups, a result first proved by McDiarmid and Skerman, here obtained from the graphon framework.
--
--   **Formalization Note** $G$ is a simple graph on a finite vertex type $V$ and $G[b]$ is `blowUp G b` on $V\times$`Fin b`. The first clause asserts that the limit exists and equals $q^*_{\mathrm{frac}}(G)$.
--
--   Differences from the source:
--   - encoding: any graph G; G[b] on the vertex set V(G) × [b] → G : SimpleGraph V with [Fintype V]; blowUp G b = G.comap Prod.fst on V × Fin b; reason: the same objects
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813a65d248922299a3380e10f238dbc5dcd3be060f7810b462bd5d3d10f), Theorem 5.22, p.66 (PDF p.66)

import Mathlib
import Definitions.Def_GraphonCheeger_Supplement_graphModularity

open Filter Topology

universe u

namespace GraphonCheeger.Supplement

/-- Theorem 5.22, p.66 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): for any graph `G`,
`q*_frac(G) = lim_{b→∞} q*(G[b]) = sup_{b ≥ 1} q*(G[b])` (5.99). Furthermore,
`q*_frac(G[b]) = q*_frac(G)` for every `b ≥ 1`.

**Formalization Note.** `G` is a simple graph on a finite vertex type `V`; `G[b]` is `blowUp G b`
on `V × Fin b`. The first clause asserts that the limit exists and equals `q*_frac(G)`. -/
theorem theorem_5_22 {V : Type u} [Fintype V] (G : SimpleGraph V) :
    Tendsto (fun b : ℕ => modularity (blowUp G b)) atTop (𝓝 (modularityFrac G)) ∧
    modularityFrac G = sSup {r : ℝ | ∃ b : ℕ, 1 ≤ b ∧ r = modularity (blowUp G b)} ∧
    ∀ b : ℕ, 1 ≤ b → modularityFrac (blowUp G b) = modularityFrac G := by sorry

end GraphonCheeger.Supplement
