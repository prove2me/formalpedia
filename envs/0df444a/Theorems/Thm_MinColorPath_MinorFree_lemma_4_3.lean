-- Prove2me | Theorems.Thm_MinColorPath_MinorFree_lemma_4_3
-- name    : MinColorPath.MinorFree.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:13:48.120215+00:00
-- url     : https://prove2.me/theorems/885b2363-6040-4910-9e42-03bda01eace0
-- title:
--   Lemma 4.3 — covering sets of the two children plus cl′(β(x)) cover x
-- statement:
--   In the context of §4 — $\pi$ an $(s,t)$-path of the colored graph $\mathcal G$, $(T,\beta)$ a $(w,c)$-good binary tree decomposition of its $0$-diagram — let $x$ be a node with two children $x',x''$, and let $Q',Q''\subseteq P$ cover $x'$ and $x''$ respectively. Then
--   $$Q'\cup Q''\cup\mathrm{cl}'(\beta(x))\ \text{covers } x.$$
--   This is the combine step's correctness: a covering set of a node is assembled from covering sets of its children and the colors of its bag.
--
--   Differences from the source:
--   - reading: the standing context of §4 (p. 21): π ∈ Π_{w,c}, D its 0-diagram, T a (w, c)-good binary tree decomposition of D → hypotheses π.IsPath, 𝒯 : RTD (pathDiag cl 0 π), 𝒯.IsBinary, IsGood 𝒯 w c and IsColoredGraph G P cl; reason: Lemmas 4.1–4.4 are stated in this context (p. 21–22); the lemma's sentence omits it
--   - reading: x′, x′′ ∈ V(T) the two children of x → x′, x′′ ∈ children x with x′ ≠ x′′; reason: in a binary tree two distinct children are all the children
--   - encoding: a finite simple graph G with palette P and coloring cl : V(G) → 2^P → a SimpleGraph V on a finite type V, colors in a type C, palette P : Finset C, cl : V → Finset C, with IsColoredGraph G P cl (cl v ⊆ P; V_τ nonempty and G[V_τ] preconnected for τ ∈ P); reason: the definition of p. 17 written on types; the same instances
--   - encoding: a rooted (binary) tree decomposition (T, β) → RTD: the published IsTreeDecomposition on a finite node type plus a root; T_x, γ(x), children and height defined from the root paths; binary = at most two children; reason: the path condition (iii) of the published definition is equivalent to the connected-subtree condition; finite trees as in the paper
--   - encoding: the d-diagram D with vertex set V(G′) ∪ P′, cl′(v) = cl(v), cl′(τ) = {τ}; s, t ∈ β(x) → diagGraph cl d H on the sum type ↥V(G′) ⊕ ↥P′ (G′ = π.toSubgraph for a path), coloring diagCl; s ∈ β(x) is baseIn (the base copy of s lies in the bag); reason: the vertex set is a disjoint union of the base part and the color part
--   - encoding: an (s, t)-path π and its x-segments, the connected components of π[γ(x)] → π : G.Walk s t with π.IsPath; x-segments are the maximal runs [i, j] of consecutive positions of π.support (0-based, from the s-side) inside γ(x); reason: the edges of a path are its consecutive pairs, so the components of π[γ(x)] are exactly these runs
--   - encoding: cdist(G, s, t), the minimum colored length of an (s, t)-path → cdist G cl s t : ℕ∞, ⊤ when there is no path; G − Q is the coloring fun v => cl v \ Q; reason: the minimum over the empty set is +∞; G − Q changes only the coloring
-- source:
--   Ajaykrishnan E S, Lokshtanov, Saurabh, Xue, Algorithms for Min-Color Path with Bounded Color-Degree, STOC 2027 submission (manuscript sha256 a088a67b…), p. 22, Lemma 4.3

import Mathlib
import Definitions.Def_MinColorPath_MinorFree_CombineFilter

set_option autoImplicit false

namespace MinColorPath.MinorFree

/-- **Lemma 4.3** (p. 22). In the §4 context (`π` an `(s, t)`-path, `T` a `(w, c)`-good binary
tree decomposition of its 0-diagram), if `x'` and `x''` are the two children of `x`, `Q'` covers
`x'` and `Q''` covers `x''`, then `Q' ∪ Q'' ∪ cl'(β(x))` covers `x`. -/
theorem lemma_4_3 {V C : Type} [Fintype V] [DecidableEq V] [DecidableEq C]
    (G : SimpleGraph V) (P : Finset C) (cl : V → Finset C) (hG : IsColoredGraph G P cl)
    (s t : V) (w c : ℕ) (π : G.Walk s t) (hπ : π.IsPath) (𝒯 : RTD (pathDiag cl 0 π))
    (hbin : 𝒯.IsBinary) (hgood : IsGood 𝒯 w c)
    (x x' x'' : 𝒯.T) (hx' : x' ∈ 𝒯.children x) (hx'' : x'' ∈ 𝒯.children x) (hne : x' ≠ x'')
    (Q' Q'' : Finset C) (hQ' : Q' ⊆ P) (hQ'' : Q'' ⊆ P)
    (hcov' : Covers G cl 𝒯 Q' x') (hcov'' : Covers G cl 𝒯 Q'' x'') :
    Covers G cl 𝒯 (Q' ∪ Q'' ∪ colSet (diagCl cl π.toSubgraph) (𝒯.bag x)) x := by sorry

end MinColorPath.MinorFree
