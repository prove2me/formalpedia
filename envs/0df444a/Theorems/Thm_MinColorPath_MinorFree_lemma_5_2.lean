-- Prove2me | Theorems.Thm_MinColorPath_MinorFree_lemma_5_2
-- name    : MinColorPath.MinorFree.lemma_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:13:15.587418+00:00
-- url     : https://prove2.me/theorems/17716b9b-a28f-4b48-8392-cab7be878eac
-- title:
--   Lemma 5.2 — the diagram of a min-color path in a clean colored graph is not well-linked
-- statement:
--   Let $\mathcal G=(G,P,\mathrm{cl})$ be a clean colored graph with $s,t\in V(G)$ and $\pi$ a min-color $(s,t)$-path. Then the diagram $\mathcal D$ of $\pi$ in $\mathcal G$ is **not well-linked**: there is no $P^\star\subseteq P'$ with $|P^\star|\ge20(\mathrm{cdeg}(\mathcal G)+1)^3$ such that every $(\mathcal F_{P_1},\mathcal F_{P_2})$-separator $S$ (for nonempty $P_1,P_2\subseteq P^\star$) has
--   $$\mathrm{cov}_{\mathcal F}(S)\ge\min\{|P_1|,|P_2|\}.$$
--   It is the heart of the structure theorem: optimality of $\pi$ forbids large well-linked color sets.
--
--   Differences from the source:
--   - encoding: G clean (p. 19): {v : cl(v) = ∅} = {s, t} → IsClean cl s t with explicit terminals s t; reason: cleanliness is defined relative to the terminals
--   - encoding: a min-color (s, t)-path π → IsMinColorPath cl π: π.IsPath and its colored length (as ℕ∞) equals cdist G cl s t; reason: the definition of p. 17
--   - encoding: a finite simple graph G with palette P and coloring cl : V(G) → 2^P → a SimpleGraph V on a finite type V, colors in a type C, palette P : Finset C, cl : V → Finset C, with IsColoredGraph G P cl (cl v ⊆ P; V_τ nonempty and G[V_τ] preconnected for τ ∈ P); reason: the definition of p. 17 written on types; the same instances
--   - encoding: the d-diagram D with vertex set V(G′) ∪ P′, cl′(v) = cl(v), cl′(τ) = {τ}; s, t ∈ β(x) → diagGraph cl d H on the sum type ↥V(G′) ⊕ ↥P′ (G′ = π.toSubgraph for a path), coloring diagCl; s ∈ β(x) is baseIn (the base copy of s lies in the bag); reason: the vertex set is a disjoint union of the base part and the color part
--   - encoding: cdist(G, s, t), the minimum colored length of an (s, t)-path → cdist G cl s t : ℕ∞, ⊤ when there is no path; G − Q is the coloring fun v => cl v \ Q; reason: the minimum over the empty set is +∞; G − Q changes only the coloring
-- source:
--   Ajaykrishnan E S, Lokshtanov, Saurabh, Xue, Algorithms for Min-Color Path with Bounded Color-Degree, STOC 2027 submission (manuscript sha256 a088a67b…), p. 27, Lemma 5.2 and the definition of well-linked before it

import Mathlib
import Definitions.Def_MinColorPath_MinorFree_StarFamily

set_option autoImplicit false

namespace MinColorPath.MinorFree

/-- **Lemma 5.2** (p. 27). For a clean colored graph `G` and a min-color `(s, t)`-path `π`, the
diagram of `π` in `G` is not well-linked. -/
theorem lemma_5_2 {V C : Type} [Fintype V] [DecidableEq V] [DecidableEq C]
    (G : SimpleGraph V) (P : Finset C) (cl : V → Finset C) (hG : IsColoredGraph G P cl)
    (s t : V) (hclean : IsClean cl s t) (π : G.Walk s t) (hπ : IsMinColorPath cl π) :
    ¬ WellLinked P cl π.toSubgraph := by sorry

end MinColorPath.MinorFree
