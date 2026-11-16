-- Prove2me | Theorems.Thm_OnlineThreeColorBounds_LowerBound_Supplement_cbip_growth
-- name    : OnlineThreeColorBounds.LowerBound.Supplement.cbip_growth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:38:39.176964+00:00
-- url     : https://prove2.me/theorems/3da92d5c-99c6-45b7-96f3-3f77a049af5d
-- title:
--   Lemma 3.2 — CBIP growth
-- statement:
--   Let $G$ be a bipartite graph whose vertices arrive in the order $0,1,\dots,n-1$, and run the online algorithm CBIP on it. Suppose CBIP gives color $a\ge 2$ to vertex $i$. Let $t\ge i$ be any later time, and let $K$ be the connected component of $i$ in the graph revealed through arrival $t$. Then each of the two sides of $K$ has at least
--   $$2^{\lfloor a/2\rfloor-1}$$
--   vertices. One side is the vertices joined to $i$ by an even walk, the other the vertices joined to $i$ by an odd walk.
--
--   So CBIP can use a large color only on a large component. With Lemma 3.1, this gives Corollary 3.3: when CBIP needs a color above the budget $q$ inside the neighborhood of an anchor, the vertex's offline-monochromatic class contains at least $k$ labels.
--
--   **Formalization Note** CBIP is run with the published deterministic `run` on the arrival-indexed graph `G : SimpleGraph (Fin n)`, and bipartiteness is `G.Colorable 2`. The graph revealed through arrival $t$ is `G.induce {j | j ≤ t}`. The sides are `evenSide` and `oddSide` of $i$ in that graph, and they are counted with `Set.ncard` (all sets are finite). The exponent is the natural number $\lfloor a/2\rfloor-1$, computed as `a / 2 - 1`, which is not truncated because $a\ge2$.
--
--   Differences from the source:
--   - encoding: an online bipartite graph and the CBIP run on it → G : SimpleGraph (Fin n) with arrival order the order of Fin n, G.Colorable 2, and the base run of the rule cbip; reason: arrival indices encode every finite ordered graph, and the run reveals exactly the earlier neighbors of each arrival
--   - reading: CBIP uses color a on a connected component; each side of that component → for every vertex i colored a and every time t ≥ i, both sides of the component of i in the graph revealed through t; reason: the source fixes no moment, and components and their sides only grow; t = i is the moment the color is used and t = n − 1 is the final graph
--   - encoding: sides of a connected bipartite component → vertices joined to i by even, respectively odd, walks; reason: in a connected bipartite graph these are exactly its two bipartition classes
-- source:
--   Yaqiao Li, New bounds for online coloring three-colorable graphs, STOC 2027 submission #425 (October 2026), pinned submission PDF SHA256 ca491d3191fa544c55ed3f45022e4cb14e5570bbd8b8bfb36e98205a8a5c518a, Lemma 3.2 (CBIP growth), §3.4, printed p. 14 / PDF p. 15 (proof printed pp. 14–15 / PDF pp. 15–16); CBIP rule (3.3), printed p. 13 / PDF p. 14

import Definitions.Def_OnlineThreeColorBounds_LowerBound_Supplement_Graphs
set_option autoImplicit false

namespace OnlineThreeColorBounds.LowerBound.Supplement

open OnlineThreeColorBounds.LowerBound

/-- Lemma 3.2 (CBIP growth), printed p. 14 / PDF p. 15. Run plain CBIP on a bipartite ordered
graph `G` (arrival order = order of `Fin n`). If arrival `i` receives color `a ≥ 2`, then at every
time `t ≥ i` the connected component of `i` in the graph revealed through arrival `t` has at least
`2 ^ (⌊a/2⌋ - 1)` vertices on each side: on the side of `i` (even walks from `i`) and on the
opposite side (odd walks from `i`). -/
theorem cbip_growth {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.Colorable 2)
    (i t : Fin n) (hit : i ≤ t) (a : ℕ) (ha : 2 ≤ a)
    (hcol : a ∈ colorsAt (run cbip G) i.val) :
    2 ^ (a / 2 - 1) ≤
        (evenSide (G.induce {j : Fin n | j ≤ t}) ⟨i, hit⟩).ncard ∧
      2 ^ (a / 2 - 1) ≤
        (oddSide (G.induce {j : Fin n | j ≤ t}) ⟨i, hit⟩).ncard := by sorry

end OnlineThreeColorBounds.LowerBound.Supplement
