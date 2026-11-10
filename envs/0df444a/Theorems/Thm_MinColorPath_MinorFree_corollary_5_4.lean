-- Prove2me | Theorems.Thm_MinColorPath_MinorFree_corollary_5_4
-- name    : MinColorPath.MinorFree.corollary_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:12:57.578263+00:00
-- url     : https://prove2.me/theorems/6928fc00-ab9d-40d4-823b-ef70b4ea14ee
-- title:
--   Corollary 5.4 — the diagram of a min-color path (clean case) has a binary tree decomposition of chromatic width ≤ 40(cdeg+1)^4
-- statement:
--   Let $\mathcal G$ be a clean colored graph with $s,t\in V(G)$ and $\pi$ a min-color $(s,t)$-path. The diagram of $\pi$ in $\mathcal G$ admits a binary tree decomposition $(T,\beta)$ with $s,t\in\beta(x)$ for all $x$ and chromatic width
--   $$\max_x|\mathrm{cl}'(\beta(x))|\le40\,(\mathrm{cdeg}(\mathcal G)+1)^4.$$
--   It is the clean case of the main structure theorem (Theorem 2.2).
--
--   Differences from the source:
--   - encoding: G clean (p. 19): {v : cl(v) = ∅} = {s, t} → IsClean cl s t with explicit terminals s t; reason: cleanliness is defined relative to the terminals
--   - encoding: a min-color (s, t)-path π → IsMinColorPath cl π: π.IsPath and its colored length (as ℕ∞) equals cdist G cl s t; reason: the definition of p. 17
--   - encoding: a finite simple graph G with palette P and coloring cl : V(G) → 2^P → a SimpleGraph V on a finite type V, colors in a type C, palette P : Finset C, cl : V → Finset C, with IsColoredGraph G P cl (cl v ⊆ P; V_τ nonempty and G[V_τ] preconnected for τ ∈ P); reason: the definition of p. 17 written on types; the same instances
--   - encoding: a rooted (binary) tree decomposition (T, β) → RTD: the published IsTreeDecomposition on a finite node type plus a root; T_x, γ(x), children and height defined from the root paths; binary = at most two children; reason: the path condition (iii) of the published definition is equivalent to the connected-subtree condition; finite trees as in the paper
--   - encoding: the d-diagram D with vertex set V(G′) ∪ P′, cl′(v) = cl(v), cl′(τ) = {τ}; s, t ∈ β(x) → diagGraph cl d H on the sum type ↥V(G′) ⊕ ↥P′ (G′ = π.toSubgraph for a path), coloring diagCl; s ∈ β(x) is baseIn (the base copy of s lies in the bag); reason: the vertex set is a disjoint union of the base part and the color part
--   - encoding: cdist(G, s, t), the minimum colored length of an (s, t)-path → cdist G cl s t : ℕ∞, ⊤ when there is no path; G − Q is the coloring fun v => cl v \ Q; reason: the minimum over the empty set is +∞; G − Q changes only the coloring
-- source:
--   Ajaykrishnan E S, Lokshtanov, Saurabh, Xue, Algorithms for Min-Color Path with Bounded Color-Degree, STOC 2027 submission (manuscript sha256 a088a67b…), p. 30, Corollary 5.4

import Mathlib
import Definitions.Def_MinColorPath_MinorFree_TreeDecomposition

set_option autoImplicit false

namespace MinColorPath.MinorFree

/-- **Corollary 5.4** (p. 30). For a clean colored graph `G` and a min-color `(s, t)`-path `π`, the
diagram of `π` admits a binary tree decomposition of chromatic width at most
`40 (cdeg(G) + 1)^4` with `s, t` in every bag. -/
theorem corollary_5_4 {V C : Type} [Fintype V] [DecidableEq V] [DecidableEq C]
    (G : SimpleGraph V) (P : Finset C) (cl : V → Finset C) (hG : IsColoredGraph G P cl)
    (s t : V) (hclean : IsClean cl s t) (π : G.Walk s t) (hπ : IsMinColorPath cl π) :
    ∃ 𝒯 : RTD (pathDiag cl 1 π), 𝒯.IsBinary ∧ diagWidth 𝒯 ≤ 40 * (cdeg P cl + 1) ^ 4 ∧
      TerminalsInBags 𝒯 s t := by sorry

end MinColorPath.MinorFree
