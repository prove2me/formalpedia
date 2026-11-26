-- Prove2me | Theorems.Thm_LefebvreVariations_triangle_ramsey_three_colours_ge_17
-- name    : LefebvreVariations.triangle_ramsey_three_colours_ge_17
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:46:23.276863+00:00
-- url     : https://prove2.me/theorems/6ca7628a-d622-59a2-b47a-09a95875805e
-- title:
--   Lefebvre's variations, No. 90 — on a theme by Erdős: the 3-colour triangle Ramsey number is at least 17
-- statement:
--   $$R_3\ \ge\ 17,$$
--   where $R_k$ is the least $n$ such that every $k$-colouring of the edges of $K_n$ contains a monochromatic triangle.
--
--   That is, the edges of $K_{16}$ can be coloured with $3$ colours so that no triangle is monochromatic. This is the classical value $R_3=R(3,3,3)=17$ of Greenwood and Gleason (1955), whose lower half is the explicit colouring of $K_{16}$ by cubic classes in $\mathbb{F}_{16}$.
--
--   **Formalization Note** The statement is `17 ≤ Erdos183.triangleRamseyNumber 3` in the platform definitions `Def_erdos183_core`, where `triangleRamseyNumber k` is the infimum of the `n` such that no `TopEdgeLabeling (Fin n) (Fin k)` is triangle-free in every colour. It needs a `3`-colouring of the edges of $K_{16}$ with no monochromatic triangle.
--
--   **Why this is a variation.** This is a variation of Erdős Problem 183 on the platform, about how fast the multicolour triangle Ramsey numbers $R_k$ grow. It is the first non-trivial size: the exact lower bound $R_3\ge 17$ in the parent's own definition `Erdos183.triangleRamseyNumber`, given by an explicit $3$-colouring of $K_{16}$. Settling it produces the base construction from which product and recursive colourings of the parent are built.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   R. E. Greenwood and A. M. Gleason, Combinatorial relations and chromatic graphs, Canadian Journal of Mathematics 7 (1955), 1-7, where R(3,3,3)=17 is proved (cited from memory, not re-checked). Witness: the vertices of K_16 are the elements of GF(16), and the edge {a,b} gets colour log(a-b) mod 3 with respect to a primitive element; no monochromatic triangle, verified by brute force while preparing this statement. Origin: the first non-trivial size of the platform problem Erdos183 (multicolour triangle Ramsey numbers), stated in its own definitions.

import Definitions.Def_erdos183_core

set_option autoImplicit false

namespace LefebvreVariations

/-- Lower half of the classical value `R(3,3,3) = 17` of the multicolour triangle Ramsey number
`R_3` of Erdős Problem 183: the edges of `K_16` can be `3`-coloured with no monochromatic
triangle, so `R_3 ≥ 17`. A witness is the Clebsch/Greenwood–Gleason colouring of `GF(16)`:
colour `{a,b}` by the class of `log (a - b)` modulo `3` (checked by brute force).
Source: Greenwood and Gleason, "Combinatorial relations and chromatic graphs", Canad. J. Math. 7
(1955), 1-7, where `R(3,3,3) = 17` is proved. -/
theorem triangle_ramsey_three_colours_ge_17 : 17 ≤ Erdos183.triangleRamseyNumber 3 := by
  sorry

end LefebvreVariations
