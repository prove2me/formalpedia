-- Prove2me | Theorems.Thm_OPG1808_order_eight_to_eleven_cycle_predecessor_reachable
-- name    : OPG1808.order_eight_to_eleven_cycle_predecessor_reachable
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T01:16:29.305655+00:00
-- url     : https://prove2.me/theorems/0e61f60b-2fb6-4669-a700-21d27396b433
-- title:
--   A cycle on eight to eleven vertices has a monochromatically reachable predecessor
-- statement:
--   Let $8\le m\le11$. Let $D$ be a tournament on the labelled vertices $\mathrm{Fin}(m)$, and assign one of three colors to every arc. Assume that $D$ has no directed triangle with three pairwise distinct arc colors, and that all forward cyclic arcs are present. Then some cyclic successor reaches its predecessor by a directed path of one color:
--
--   $$
--   \begin{gathered}
--   8\le m\le11,\qquad
--   D(i,i+1)\quad\text{for every }i\in\mathbb Z/m\mathbb Z,\\
--   \text{no rainbow directed triangle}
--   \quad\Longrightarrow\quad
--   \exists i\in\mathbb Z/m\mathbb Z,\quad
--    i+1\leadsto i\ \text{monochromatically}.
--   \end{gathered}
--   $$
--
--   The path may use any vertices of this labelled tournament. The color may be any of the three colors, and unused colors are allowed. This is the remaining finite cycle obstruction for the order-eleven target after the checked case through seven vertices has been separated. The hypotheses are precisely the stated cardinal bounds, tournament structure, absence of rainbow directed triangles, and the forward cycle arcs.
-- source:
--   Derived finite cycle-exclusion residual for OPG1808.order_eleven, https://prove2.me/theorems/a73da177-e54a-4f2b-872f-7a6232e852b8, after separating OPG1808.order_seven. The reduction uses OPG1808.missing_predecessor_cycle_of_no_source, https://prove2.me/theorems/761b9151-9091-4494-9871-dd94b246b259. Obstruction-cycle framework: Georgakopoulos--Sprüssel, On 3-coloured tournaments, https://arxiv.org/abs/0904.1967v2, pp.2--3. The finite range eight through eleven is a separate formalization residual, not a theorem quoted from that paper.

import Definitions.Def_opg1808_colored_tournaments
import Mathlib.Logic.Equiv.Fin.Rotate

open OPG1808

theorem OPG1808.order_eight_to_eleven_cycle_predecessor_reachable
    (m : ℕ) (hm : 8 ≤ m) (horder : m ≤ 11)
    (D : Digraph (Fin m)) (color : ArcColoring (Fin m))
    (htournament : IsTournament D)
    (hnoRainbow : ¬HasRainbowDirectedTriangle D color)
    (hcycle : ∀ i : Fin m, D i (finRotate m i)) :
    ∃ i : Fin m, MonochromaticallyReaches D color (finRotate m i) i := by sorry
