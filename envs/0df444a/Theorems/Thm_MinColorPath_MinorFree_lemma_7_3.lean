-- Prove2me | Theorems.Thm_MinColorPath_MinorFree_lemma_7_3
-- name    : MinColorPath.MinorFree.lemma_7_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:13:29.378359+00:00
-- url     : https://prove2.me/theorems/286936b5-d69e-4179-8f8c-4c8fdceef427
-- title:
--   Lemma 7.3 — color closure, color expansion and strong base closure of a tree decomposition are tree decompositions
-- statement:
--   Let $\mathcal D$ be the $d$-diagram of a subgraph $G'$ of the semi-clean colored graph $\mathcal G$ and $(T,\beta)$ a tree decomposition of $D$ of chromatic width $w$. Then, with one absolute constant $K$: (i) the color closure of $(T,\beta)$ is a tree decomposition of $D$ of chromatic width $w$; (ii) its color expansion is a tree decomposition of chromatic width at most $w\,(\mathrm{cdeg}(\mathcal G)+1)^{Kd}$; (iii) its strong base closure is a tree decomposition of chromatic width at most
--   $$K\,w\,(\mathrm{cdeg}(\mathcal G)+1).$$
--   These operations prepare the decomposition used for Theorem 7.1.
--
--   Differences from the source:
--   - reading: the standing context of §7 (p. 41): G = (G, P, cl) is a semi-clean colored graph with s, t ∈ V(G) → hypotheses IsColoredGraph G P cl and IsSemiClean G cl s t; reason: §7 fixes this context once at its top (p. 41); the lemma's sentence omits it
--   - reading: chromatic width w·(cdeg(G)+1)^{O(d)} in (ii) and O(w·(cdeg(G)+1)) in (iii) → ≤ w · (cdeg + 1)^{K·d} and ≤ K · w · (cdeg + 1), one K : ℕ quantified before every type and graph; reason: the O(·) of the page with an absolute constant; at d = 0 the color expansion adds nothing, so the exponent needs no additive constant
--   - reading: (i) 'with chromatic width w' → the color closure's width equals w; reason: the color closure adds only colors already carried by the bag, so equality is what the page states
--   - reading: (ii) 'For an integer r ≥ 0, the color expansion …' → no parameter r; reason: r occurs nowhere else in the statement; it binds nothing
--   - encoding: the color closure / expansion / strong base closure of T in D → the published IsTreeDecomposition for the same tree with the bags replaced by the operation of each bag; widths via widthAfter; reason: the bagwise definition of p. 43
--   - encoding: a finite simple graph G with palette P and coloring cl : V(G) → 2^P → a SimpleGraph V on a finite type V, colors in a type C, palette P : Finset C, cl : V → Finset C, with IsColoredGraph G P cl (cl v ⊆ P; V_τ nonempty and G[V_τ] preconnected for τ ∈ P); reason: the definition of p. 17 written on types; the same instances
--   - encoding: a rooted (binary) tree decomposition (T, β) → RTD: the published IsTreeDecomposition on a finite node type plus a root; T_x, γ(x), children and height defined from the root paths; binary = at most two children; reason: the path condition (iii) of the published definition is equivalent to the connected-subtree condition; finite trees as in the paper
--   - encoding: the d-diagram D with vertex set V(G′) ∪ P′, cl′(v) = cl(v), cl′(τ) = {τ}; s, t ∈ β(x) → diagGraph cl d H on the sum type ↥V(G′) ⊕ ↥P′ (G′ = π.toSubgraph for a path), coloring diagCl; s ∈ β(x) is baseIn (the base copy of s lies in the bag); reason: the vertex set is a disjoint union of the base part and the color part
-- source:
--   Ajaykrishnan E S, Lokshtanov, Saurabh, Xue, Algorithms for Min-Color Path with Bounded Color-Degree, STOC 2027 submission (manuscript sha256 a088a67b…), p. 43, Lemma 7.3

import Mathlib
import Definitions.Def_MinColorPath_MinorFree_Closures

set_option autoImplicit false

namespace MinColorPath.MinorFree

/-- **Lemma 7.3** (p. 43). There is an absolute constant `K` such that: for a semi-clean colored
graph `G`, the `d`-diagram `D` of a subgraph `G'` and a tree decomposition `T` of `D` of chromatic
width `w`, (i) the color closure of `T` is a tree decomposition of `D` of chromatic width `w`,
(ii) its color expansion is one of chromatic width at most `w (cdeg(G) + 1)^{K d}`, and (iii) its
strong base closure is one of chromatic width at most `K w (cdeg(G) + 1)`. -/
theorem lemma_7_3 :
    ∃ K : ℕ, ∀ (V C : Type) [Fintype V] [DecidableEq V] [DecidableEq C]
      (G : SimpleGraph V) (P : Finset C) (cl : V → Finset C), IsColoredGraph G P cl →
      ∀ s t : V, IsSemiClean G cl s t →
      ∀ (H : G.Subgraph) (d : ℕ) (𝒯 : RTD (diagGraph cl d H)) (w : ℕ), diagWidth 𝒯 = w →
        (RobertsonSeymour1986.GM5.IsTreeDecomposition (diagGraph cl d H) 𝒯.t
            (fun x => colorClosure cl H (𝒯.bag x)) ∧
          widthAfter cl H 𝒯 (colorClosure cl H) = w) ∧
        (RobertsonSeymour1986.GM5.IsTreeDecomposition (diagGraph cl d H) 𝒯.t
            (fun x => colorExpansion cl H d (𝒯.bag x)) ∧
          widthAfter cl H 𝒯 (colorExpansion cl H d) ≤ w * (cdeg P cl + 1) ^ (K * d)) ∧
        (RobertsonSeymour1986.GM5.IsTreeDecomposition (diagGraph cl d H) 𝒯.t
            (fun x => strongBaseClosure cl H (𝒯.bag x)) ∧
          widthAfter cl H 𝒯 (strongBaseClosure cl H) ≤ K * w * (cdeg P cl + 1)) := by sorry

end MinColorPath.MinorFree
