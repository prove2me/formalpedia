-- Prove2me | Theorems.Thm_MinColorPath_MinorFree_theorem_7_1
-- name    : MinColorPath.MinorFree.theorem_7_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:12:55.539232+00:00
-- url     : https://prove2.me/theorems/e39195a0-b246-4c54-a5bb-d8e91ab29b7b
-- title:
--   Theorem 7.1 — K_{3,h}-minor-free: a min-color path with bounded chromatic width and crossing number for every d (as printed; see insight I2)
-- statement:
--   Let $h\in\mathbb N_0$ be fixed and $\mathcal G=(G,P,\mathrm{cl})$ a semi-clean colored graph with $s,t\in V(G)$ whose base graph $G$ has no $K_{3,h}$ minor. Then there is a min-color $(s,t)$-path $\pi$ such that for every $d\in\mathbb N_0$ the $d$-diagram of $\pi$ admits a binary tree decomposition $(T,\beta)$ with $s,t\in\beta(x)$ for all $x$, whose chromatic width and crossing number of $\pi$ are both
--   $$(\mathrm{cdeg}(\mathcal G)+1)^{O(d+1)},$$
--   read as at most $K(\mathrm{cdeg}(\mathcal G)+1)^{K(d+1)}$ with $K$ depending only on $h$. With $d=0$ it supplies hypothesis (*) of Theorem 2.1 for the proof of Theorem 1.1. As printed the statement asserts that a min-color path exists even when $s$ and $t$ are disconnected; it is stated as printed (insight I2).
--
--   Differences from the source:
--   - reading: (cdeg(G)+1)^{O(d+1)} for the chromatic width and for the crossing number → ≤ K · (cdeg + 1)^{K·(d+1)}, one K : ℕ for each h, chosen before every type, graph, path and d; reason: §7 says its O(·) hide constants depending on h (p. 41); the paper's convention for X^{O(1)}
--   - encoding: K3,h-minor-free → ¬ IsMinor (completeBipartiteGraph (Fin 3) (Fin h)) G with the published IsMinor; reason: the published branch-set definition; h ∈ ℕ includes 0 as printed
--   - encoding: a min-color (s, t)-path π → IsMinColorPath cl π: π.IsPath and its colored length (as ℕ∞) equals cdist G cl s t; reason: the definition of p. 17
--   - encoding: a finite simple graph G with palette P and coloring cl : V(G) → 2^P → a SimpleGraph V on a finite type V, colors in a type C, palette P : Finset C, cl : V → Finset C, with IsColoredGraph G P cl (cl v ⊆ P; V_τ nonempty and G[V_τ] preconnected for τ ∈ P); reason: the definition of p. 17 written on types; the same instances
--   - encoding: a rooted (binary) tree decomposition (T, β) → RTD: the published IsTreeDecomposition on a finite node type plus a root; T_x, γ(x), children and height defined from the root paths; binary = at most two children; reason: the path condition (iii) of the published definition is equivalent to the connected-subtree condition; finite trees as in the paper
--   - encoding: the d-diagram D with vertex set V(G′) ∪ P′, cl′(v) = cl(v), cl′(τ) = {τ}; s, t ∈ β(x) → diagGraph cl d H on the sum type ↥V(G′) ⊕ ↥P′ (G′ = π.toSubgraph for a path), coloring diagCl; s ∈ β(x) is baseIn (the base copy of s lies in the bag); reason: the vertex set is a disjoint union of the base part and the color part
--   - encoding: cdist(G, s, t), the minimum colored length of an (s, t)-path → cdist G cl s t : ℕ∞, ⊤ when there is no path; G − Q is the coloring fun v => cl v \ Q; reason: the minimum over the empty set is +∞; G − Q changes only the coloring
-- source:
--   Ajaykrishnan E S, Lokshtanov, Saurabh, Xue, Algorithms for Min-Color Path with Bounded Color-Degree, STOC 2027 submission (manuscript sha256 a088a67b…), p. 41, Theorem 7.1

import Mathlib
import Definitions.Def_MinColorPath_MinorFree_TreeDecomposition
import Definitions.Def_RobertsonSeymour1986_GM5_IsMinor

set_option autoImplicit false

namespace MinColorPath.MinorFree

/-- **Theorem 7.1** (p. 41), as printed. For every `h ∈ ℕ` there is `K` such that for every
semi-clean colored graph `G` with terminals `s, t` whose base graph has no `K_{3,h}` minor there
is a min-color `(s, t)`-path `π` such that for every `d ∈ ℕ` the `d`-diagram of `π` admits a
binary tree decomposition with `s, t` in every bag, chromatic width at most
`K (cdeg(G) + 1)^{K (d+1)}` and crossing number of `π` at most `K (cdeg(G) + 1)^{K (d+1)}`. -/
theorem theorem_7_1 :
    ∀ h : ℕ, ∃ K : ℕ, ∀ (V C : Type) [Fintype V] [DecidableEq V] [DecidableEq C]
      (G : SimpleGraph V) (P : Finset C) (cl : V → Finset C), IsColoredGraph G P cl →
      ∀ s t : V, IsSemiClean G cl s t →
      ¬ RobertsonSeymour1986.GM5.IsMinor (completeBipartiteGraph (Fin 3) (Fin h)) G →
      ∃ π : G.Walk s t, IsMinColorPath cl π ∧ ∀ d : ℕ,
        ∃ 𝒯 : RTD (pathDiag cl d π), 𝒯.IsBinary ∧ TerminalsInBags 𝒯 s t ∧
          diagWidth 𝒯 ≤ K * (cdeg P cl + 1) ^ (K * (d + 1)) ∧
          pathCrossing 𝒯 ≤ K * (cdeg P cl + 1) ^ (K * (d + 1)) := by sorry

end MinColorPath.MinorFree
