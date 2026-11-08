-- Prove2me | Theorems.Thm_GraphonCheeger_eq_4_136
-- name    : GraphonCheeger.eq_4_136
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:53:25.72702+00:00
-- url     : https://prove2.me/theorems/d36a9d48-96af-47c0-9c1d-1980b42b2e64
-- title:
--   (4.136): $W_G\in\mathcal W_c$ if and only if $d_{\min}(G)\ge cn$
-- statement:
--   Let $G$ be a graph with $|G|=n\ge1$ vertices, let $W_G$ be its continuous graphon on $[0,1]$, and let $c\in[0,1]$. Then
--
--   $$W_G\in\mathcal W_c\iff d_{\min}(G)=\min_{1\le v\le n}d_v\ge cn .$$
--
--   This translates the minimum-degree hypothesis on graphs into membership of their step graphons in the class $\mathcal W_c$, which is how the convergence theorem for graphs reduces to the one for graphons.
--
--   Differences from the source:
--   - encoding: graph $G$ with $|G|=n$ → $n\ge1$ and $G$ a graph on `Fin n`; reason: $W_G$ is undefined for the empty graph (Example 2.4 splits $[0,1]$ into $|G|$ intervals), and every finite graph is isomorphic to one on `Fin n`.
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813…), Definition 4.28, (4.136), p.48

import Mathlib
import Definitions.Def_GraphonCheeger_stepGraphon
import Definitions.Def_GraphonCheeger_InWc

open MeasureTheory

namespace GraphonCheeger

/-- (4.136), Definition 4.28, p.48 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): for a graph `G` with `|G| = n`,
`W_G ∈ W_c` if and only if `d_min(G) = min_v d_v ≥ c n`.

**Formalization Note.** `0 < n`: the step graphon `W_G` of Example 2.4 is undefined for the
empty graph. `c ∈ [0, 1]` is the range of Definition 4.28. -/
theorem eq_4_136 {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (c : ℝ)
    (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    InWc volume (stepGraphon G) c ↔ ∀ v : Fin n, c * (n : ℝ) ≤ (G.degree v : ℝ) := by sorry

end GraphonCheeger
