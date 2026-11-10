-- Prove2me | Theorems.Thm_MinColorPath_MinorFree_lemma_3_4
-- name    : MinColorPath.MinorFree.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:12:26.361877+00:00
-- url     : https://prove2.me/theorems/251c54f6-692b-4530-b66a-4e8e2311f634
-- title:
--   Lemma 3.4 — endpoints of x-segments lie in β(x) ∪ {s, t}
-- statement:
--   Let $G$ be a graph, $(T,\beta)$ a (rooted) tree decomposition of $G$, $\pi$ an $(s,t)$-path of $G$ and $x$ a node of $T$. Then both endpoints of every $x$-segment of $\pi$ (connected component of $\pi[\gamma(x)]$) lie in
--   $$\beta(x)\cup\{s,t\}.$$
--   This is the basic fact behind the dynamic programming of Combine&Filter: segments enter and leave $\gamma(x)$ only through the bag of $x$.
--
--   Differences from the source:
--   - encoding: a graph G → a SimpleGraph V on a finite type V; reason: graphs of the paper are finite
--   - encoding: a rooted (binary) tree decomposition (T, β) → RTD: the published IsTreeDecomposition on a finite node type plus a root; T_x, γ(x), children and height defined from the root paths; binary = at most two children; reason: the path condition (iii) of the published definition is equivalent to the connected-subtree condition; finite trees as in the paper
--   - encoding: an (s, t)-path π and its x-segments, the connected components of π[γ(x)] → π : G.Walk s t with π.IsPath; x-segments are the maximal runs [i, j] of consecutive positions of π.support (0-based, from the s-side) inside γ(x); reason: the edges of a path are its consecutive pairs, so the components of π[γ(x)] are exactly these runs
-- source:
--   Ajaykrishnan E S, Lokshtanov, Saurabh, Xue, Algorithms for Min-Color Path with Bounded Color-Degree, STOC 2027 submission (manuscript sha256 a088a67b…), p. 19, Lemma 3.4

import Mathlib
import Definitions.Def_MinColorPath_MinorFree_TreeDecomposition

set_option autoImplicit false

namespace MinColorPath.MinorFree

/-- **Lemma 3.4** (p. 19). For a tree decomposition `T = (T, β)` of a graph `G`, an
`(s, t)`-path `π` of `G` and a node `x`, both endpoints of every `x`-segment of `π` lie in
`β(x) ∪ {s, t}`. -/
theorem lemma_3_4 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (𝒯 : RTD G)
    {s t : V} (π : G.Walk s t) (hπ : π.IsPath) (x : 𝒯.T) (i j : Fin π.support.length)
    (hseg : 𝒯.IsSegment (fun B v => v ∈ B) π.support x i j) :
    (π.support.get i ∈ 𝒯.bag x ∨ π.support.get i = s ∨ π.support.get i = t) ∧
      (π.support.get j ∈ 𝒯.bag x ∨ π.support.get j = s ∨ π.support.get j = t) := by sorry

end MinColorPath.MinorFree
