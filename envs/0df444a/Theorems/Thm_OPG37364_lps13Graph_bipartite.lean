-- Prove2me | Theorems.Thm_OPG37364_lps13Graph_bipartite
-- name    : OPG37364.lps13Graph_bipartite
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T14:44:33.799392+00:00
-- url     : https://prove2.me/theorems/5159a1d2-fdcb-4f43-8bb2-557a2247efb3
-- title:
--   Bipartiteness of the fixed-p=13 LPS Cayley graph on PGL₂
-- statement:
--   Let $q>13$ be prime and choose $i\in\mathbb F_q$ with $i^2=-1$. Consider the fixed-$p=13$ graph `OPG37364.lps13Graph`, on $\operatorname{PGL}_2(\mathbb F_q)$ with the fourteen norm-$13$ quaternion generators specified in `Definitions.Def_opg37364_lps13`. If $13$ is a quadratic nonresidue modulo $q$, then this graph is bipartite: there is a Boolean coloring of its projective vertices for which the endpoints of every edge have different colors.
--
--   The coloring records whether the determinant of a matrix representative is a square. This is well-defined because multiplying a representative by a nonzero scalar multiplies its determinant by a square. Every generator has determinant $13$, so multiplication by a generator exchanges the two colors. The formal hypothesis is `legendreSym q 13 = -1`, with $q$ as the modulus. No connectedness assumption is required.
--
--   This is a formalization of the classical determinant-square-class bipartition for the LPS construction, specialized to the existing fixed-$13$ graph.
-- source:
--   Davidoff, Sarnak and Valette, Elementary Number Theory, Group Theory, and Ramanujan Graphs, Proposition 4.1.2(d) and Remark 4.2.3(c), printed p. 114, https://math.bme.hu/~gabor/oktatas/SztoM/DavidoffSarnakValette.pdf . The underlying fixed-p=13 convention is the PGL construction of Lubotzky, Phillips and Sarnak, Ramanujan graphs, Combinatorica 8 (1988), p. 262, https://doi.org/10.1007/BF02126799 .

import Definitions.Def_opg37364_lps13
import Mathlib.NumberTheory.LegendreSymbol.Basic
set_option autoImplicit false

namespace OPG37364

theorem lps13Graph_bipartite {q : ℕ} [Fact q.Prime]
    (hq : 13 < q) (i : LPS13Root q) (hnr : legendreSym q 13 = -1) :
    IsBipartite (lps13Graph hq i) := by sorry

end OPG37364
