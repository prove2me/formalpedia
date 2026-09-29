-- Prove2me | Theorems.Thm_OPG1808_order_eleven
-- name    : OPG1808.order_eleven
-- status  : Open
-- author  : @hao jia
-- created : 2026-09-07T07:14:18.083733+00:00
-- url     : https://prove2.me/theorems/a73da177-e54a-4f2b-872f-7a6232e852b8
-- title:
--   The three-colored tournament problem through order eleven
-- statement:
--   Let $T$ be a nonempty tournament on at most eleven vertices with its arcs colored by three colors. If $T$ has no rainbow directed triangle, then some vertex reaches every target along a monochromatic directed path:
--
--   $$
--   1\le |V(T)|\le11\ \land\ \text{no rainbow directed triangle}
--   \quad\Longrightarrow\quad
--   \exists s\ \forall t,\ s\leadsto t\text{ monochromatically}.
--   $$
--
--   The path color may depend on $t$. This finite theorem is an open formal target; the cited repository replay is `candidate_only`, not a proof on the platform.
-- source:
--   VibeMathing candidate_only exact-closure replay at commit aa702573cf51c587cccc6d31c28a54bcc64eb5d9, research/artifacts/candidates/opg1808-r05-replay-20260907/README.md; minimum-counterexample reduction: Georgakopoulos--Sprüssel, arXiv:0904.1967v2, pp. 2-3

import Definitions.Def_opg1808_colored_tournaments

namespace OPG1808

universe u

/-- The finite root case through eleven vertices. -/
theorem order_eleven
    {V : Type u} [Fintype V] [Nonempty V]
    (D : Digraph V) (color : ArcColoring V)
    (htournament : IsTournament D)
    (horder : Fintype.card V ≤ 11)
    (hnoRainbow : ¬ HasRainbowDirectedTriangle D color) :
    ∃ s : V, IsMonochromaticSource D color s := by sorry

end OPG1808
