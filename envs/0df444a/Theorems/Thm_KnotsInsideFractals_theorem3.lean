-- Prove2me | Theorems.Thm_KnotsInsideFractals_theorem3
-- name    : KnotsInsideFractals.theorem3
-- status  : Open
-- author  : @LG
-- created : 2026-11-26T15:09:50.234392+00:00
-- url     : https://prove2.me/theorems/0148a6df-5ff1-4ba9-825b-72d25a02e11d
-- title:
--   Theorem 3 (Theorem C) — the sponge is faster
-- statement:
--   **Theorem 3 (Theorem C).** For every knot $K$ that embeds in some Sierpinski iteration, the least Menger iteration needed is at most the least Sierpinski iteration needed:
--   $$M(K)\le S(K)\qquad\text{whenever }S(K)\text{ is defined}.$$
--   Here $M(K)$ (resp. $S(K)$) is the minimum number of iterations of the Menger sponge (resp. Sierpinski tetrahedron) whose $1$-skeleton contains a copy of $K$. Thus the more complicated fractal produces each knot sooner, answering the paper's second question. The inequality can be sharp: $M(3_1)=1$ while $S(3_1)\ge 2$.
-- source:
--   Broden–Espinosa–Nazareth–Voth, Knots Inside Fractals, https://arxiv.org/abs/2409.03639, §5 Theorem 3 (Theorem C), Definition 1

import Mathlib
import Definitions.Def_KnotsInsideFractals_fractals
import Definitions.Def_KnotsInsideFractals_knots
open Set KnotsInsideFractals

namespace KnotsInsideFractals
theorem theorem3 (K : PolygonalKnot) (h : ∃ n, EmbedsInSierpinski K n) : M K ≤ S K := by sorry
end KnotsInsideFractals
