-- Prove2me | Theorems.Thm_FullImmersionFPT_Main_lemma_45
-- name    : FullImmersionFPT.Main.lemma_45
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:46:57.429086+00:00
-- url     : https://prove2.me/theorems/741e32d5-f68d-44ac-ab1b-7236f7288b36
-- title:
--   Lemma 45 — a computable grid-immersion threshold for 4-regular graphs
-- statement:
--   There is a computable function $f_{45}:\mathbb N\to\mathbb N$ such that every 4-regular graph $G$ (loops and parallel edges allowed, not necessarily connected) with treewidth at least $f_{45}(t)$ contains the $t\times t$ grid as an immersion: distinct vertices of $G$ represent the $t^2$ grid vertices and pairwise edge-disjoint non-empty trails of $G$ join the representatives of adjacent grid vertices. Computability of $f_{45}$ is what keeps the main algorithm fixed-parameter tractable.
--
--   Differences from the source:
--   - reading: "contains the t × t grid as an immersion" → weak immersion: an injective vertex map and pairwise edge-disjoint non-empty trails between the images of adjacent grid vertices (internal vertices of a trail may be images); reason: footnote 3 (p. 3): "We consider weak immersions"
--   - encoding: treewidth of a graph with loops and parallel edges → treewidth of the underlying simple graph (published TreewidthLE); "treewidth at least k" = no tree-decomposition of width < k; reason: loops and parallel edges do not affect treewidth
--   - encoding: the t × t grid → published RobertsonSeymour1986.GM5.grid t on Fin t × Fin t; reason: same graph, 0-based indices
--   - encoding: graphs with loops and parallel edges, edges {h₁, h₂} of half-edges (§5) → Multigraph V H: finite vertex and half-edge sets in ambient types, inc, mate; an edge is s(h, mate h) : Sym2 H; a trail is the list of the tail half-edges of its arcs; reason: the paper's half-edge model; keeping the ambient types fixed lets splitting off delete vertices and half-edges
-- source:
--   Barabash, Geelen, McCarty, McFarland, Wollan, Finding full immersions is fixed-parameter tractable in labeled tour graphs, STOC 2027 submission (manuscript of November 2, 2026, sha256 c071967d…), p. 56, Lemma 45

import Mathlib
import Definitions.Def_FullImmersionFPT_Main_Multigraph

set_option autoImplicit false

open Classical

namespace FullImmersionFPT.Main

/-- **Lemma 45** (p. 56). There is a computable function `f₄₅ : ℕ → ℕ` such that every 4-regular
graph `G` (loops and parallel edges allowed) with treewidth at least `f₄₅(t)` contains the `t × t`
grid as an immersion. -/
theorem lemma_45 :
    ∃ f45 : ℕ → ℕ, Computable f45 ∧
      ∀ (V H : Type) (G : Multigraph V H), G.IsValid → G.IsRegular 4 → ∀ t : ℕ,
        G.TreewidthAtLeast (f45 t) → G.ImmersesSimple (RobertsonSeymour1986.GM5.grid t) := by sorry

end FullImmersionFPT.Main
