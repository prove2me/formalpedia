-- Prove2me | Theorems.Thm_MinColorPath_MinorFree_theorem_2_3
-- name    : MinColorPath.MinorFree.theorem_2_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:12:38.394403+00:00
-- url     : https://prove2.me/theorems/585952f5-7697-4be6-aba9-87efa2d3e427
-- title:
--   Theorem 2.3 — structure theorem for d-diagrams: chromatic width ≤ 40(cdeg^{2d+1}+1)^4
-- statement:
--   Let $\mathcal G$ be a semi-clean colored graph with $s,t\in V(G)$, $d\ge1$ an integer and $\pi$ a min-color $(s,t)$-path. The $d$-diagram of $\pi$ admits a binary tree decomposition of chromatic width at most
--   $$40\,(\mathrm{cdeg}(\mathcal G)^{2d+1}+1)^4$$
--   with $s,t\in\beta(x)$ and $|\beta(x)\cap V_0(\mathcal G)\setminus\{s,t\}|\le1$ for every node $x$. It extends Theorem 2.2 from diagrams to $d$-diagrams.
--
--   Differences from the source:
--   - reading: 'chromatic width 40 (…)^4' → diagWidth 𝒯 ≤ 40 * (…)^4; reason: the width is an upper bound, as in Corollary 5.4 from which the theorem is derived (p. 30)
--   - encoding: semi-clean colored graph with s, t → IsSemiClean G cl s t with explicit terminals; reason: semi-cleanliness is defined relative to the terminals
--   - encoding: a min-color (s, t)-path π → IsMinColorPath cl π: π.IsPath and its colored length (as ℕ∞) equals cdist G cl s t; reason: the definition of p. 17
--   - encoding: a finite simple graph G with palette P and coloring cl : V(G) → 2^P → a SimpleGraph V on a finite type V, colors in a type C, palette P : Finset C, cl : V → Finset C, with IsColoredGraph G P cl (cl v ⊆ P; V_τ nonempty and G[V_τ] preconnected for τ ∈ P); reason: the definition of p. 17 written on types; the same instances
--   - encoding: a rooted (binary) tree decomposition (T, β) → RTD: the published IsTreeDecomposition on a finite node type plus a root; T_x, γ(x), children and height defined from the root paths; binary = at most two children; reason: the path condition (iii) of the published definition is equivalent to the connected-subtree condition; finite trees as in the paper
--   - encoding: the d-diagram D with vertex set V(G′) ∪ P′, cl′(v) = cl(v), cl′(τ) = {τ}; s, t ∈ β(x) → diagGraph cl d H on the sum type ↥V(G′) ⊕ ↥P′ (G′ = π.toSubgraph for a path), coloring diagCl; s ∈ β(x) is baseIn (the base copy of s lies in the bag); reason: the vertex set is a disjoint union of the base part and the color part
--   - encoding: cdist(G, s, t), the minimum colored length of an (s, t)-path → cdist G cl s t : ℕ∞, ⊤ when there is no path; G − Q is the coloring fun v => cl v \ Q; reason: the minimum over the empty set is +∞; G − Q changes only the coloring
-- source:
--   Ajaykrishnan E S, Lokshtanov, Saurabh, Xue, Algorithms for Min-Color Path with Bounded Color-Degree, STOC 2027 submission (manuscript sha256 a088a67b…), p. 32, Theorem 2.3

import Mathlib
import Definitions.Def_MinColorPath_MinorFree_TreeDecomposition

set_option autoImplicit false

namespace MinColorPath.MinorFree

/-- **Theorem 2.3** (p. 32). For a semi-clean colored graph `G`, an integer `d ≥ 1` and a min-color
`(s, t)`-path `π`, the `d`-diagram of `π` admits a binary tree decomposition of chromatic width at
most `40 (cdeg(G)^{2d+1} + 1)^4` with `s, t ∈ β(x)` and `|β(x) ∩ V_0(G) \ {s, t}| ≤ 1` for every
node `x`. -/
theorem theorem_2_3 {V C : Type} [Fintype V] [DecidableEq V] [DecidableEq C]
    (G : SimpleGraph V) (P : Finset C) (cl : V → Finset C) (hG : IsColoredGraph G P cl)
    (s t : V) (hsc : IsSemiClean G cl s t) (d : ℕ) (hd : 1 ≤ d) (π : G.Walk s t)
    (hπ : IsMinColorPath cl π) :
    ∃ 𝒯 : RTD (pathDiag cl d π), 𝒯.IsBinary ∧
      diagWidth 𝒯 ≤ 40 * (cdeg P cl ^ (2 * d + 1) + 1) ^ 4 ∧
      TerminalsInBags 𝒯 s t ∧ ∀ x, extraUncolored 𝒯 s t x ≤ 1 := by sorry

end MinColorPath.MinorFree
