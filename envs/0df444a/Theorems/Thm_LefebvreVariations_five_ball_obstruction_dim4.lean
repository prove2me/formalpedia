-- Prove2me | Theorems.Thm_LefebvreVariations_five_ball_obstruction_dim4
-- name    : LefebvreVariations.five_ball_obstruction_dim4
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:30:53.247234+00:00
-- url     : https://prove2.me/theorems/0d2fe094-a096-45e2-8a24-737e7b98fa8e
-- title:
--   Lefebvre's variations, No. 210 — on a theme by Gromov: five equal balls do not pack the four-dimensional ball beyond capacity two fifths
-- statement:
--   Let five balls of capacity $c>0$ be symplectically embedded in the open ball of capacity $1$ of $\mathbb C^2$ with pairwise disjoint images: that is, there are symplectic embeddings $f_1,\dots,f_{5}$ of neighbourhoods of the closed balls $B(c)=\{z:\pi|z|^2\le c\}$ with $f_i\bigl(B(c)\bigr)\subset\{\pi|z|^2<1\}$ and $f_i\bigl(B(c)\bigr)\cap f_j\bigl(B(c)\bigr)=\emptyset$ for $i\ne j$. Then
--   $$
--   c\;\le\;\frac{2}{5}.
--   $$
--   Equivalently, at most the fraction $5\left(\frac{2}{5}\right)^2=\frac{4}{5}$ of the volume of the ball can be filled by five equal balls. The bound comes from the exceptional class $2L-E_1-\cdots-E_5$ of the blow-up of $\mathbb{CP}^2$ at 5 points, which gives the inequality $2\ge 5c$; Gromov's two-ball inequality $a+b\le1$ is the analogous statement for two balls.
--
--   **Formalization Note** The statement uses the platform definition `OAI.HigherDimensionalBallPacking.HasPacking` of `Def_BallPacking`, exactly as in `SymplecticBallPacking.two_ball_obstruction_dim4`: `HasPacking 2 5 1 (fun _ => c)` says that 5 closed balls of capacity `c` (`capacity z = π ∑ |z_j|²`) embed symplectically (`SymplecticOn`: smooth embeddings of open neighbourhoods preserving the standard form), with pairwise disjoint images, into the open ball of capacity `1`. The hypothesis `0 < c` keeps the balls non-degenerate.
--
--   **Why this is a variation.** This varies the open platform problem `SymplecticBallPacking.two_ball_obstruction_dim4`, Gromov's two-ball inequality $a+b\le1$ for symplectic packings of the four-dimensional ball. It plays the same obstruction for five equal balls, where the exceptional class $2L-E_1-\cdots-E_5$ of the blow-up of the projective plane gives the sharp bound $c\le 2/5$, with the parent's own `HasPacking` definition. It is the next obstruction in the packing-number table after the two-ball case.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   D. McDuff and L. Polterovich, Symplectic packings and algebraic geometry, Invent. Math. 115 (1994) 405-434; M. Gromov, Pseudo holomorphic curves in symplectic manifolds, Invent. Math. 82 (1985) 307-347 (page numbers not verified). Origin of this statement: the five-ball case of the symplectic packing obstruction in dimension four (platform family SymplecticBallPacking), the next sizes after SymplecticBallPacking.two_ball_obstruction_dim4 (Gromov's two-ball inequality a + b <= 1). Numerical check of the data: the class 2L - E1 - ... - E5 has self-intersection -1 and first Chern number 1, and 5 * (2/5)^2 = 4/5, the known packing number of 5 equal balls.
--    Verified by web search on 26 Nov 2026: the existence and title of McDuff-Polterovich 1994 (MaRDI record) and the packing-number table v_2..v_9 = 1/2, 3/4, 1, 4/5, 24/25, 63/64, 288/289, 1 (P. Biran, survey, https://www.math.uni-bielefeld.de/~rehmann/ECM/cdrom/3ecm/pdfs/pant3/biran.pdf, attributing it to McDuff-Polterovich). The exceptional-class description is cited from memory.

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_SymplecticBallPacking

set_option autoImplicit false

open scoped ContDiff

namespace LefebvreVariations

open OAI.HigherDimensionalBallPacking
open Set

/-- **Five equal balls do not pack `B⁴(1)` beyond capacity `2/5`.** If five disjoint symplectic images of the
closed balls of capacity `c` sit inside the open ball of capacity `1` in `ℂ²`, then `c ≤ 2/5` (so at most
`5 (2/5)² = 4/5` of the volume is filled). Obstruction from the exceptional class `2L - E₁ - … - E₅` of the
blow-up of `ℂP²` at five points (McDuff–Polterovich, Invent. Math. 115 (1994) 405–434; Biran,
Geom. Funct. Anal. 7 (1997) 420–437; both cited from memory), the five-ball analogue of Gromov's two-ball
inequality `a + b ≤ 1`.

**Formalization Note.** Uses the platform definitions `HasPacking` of `Def_BallPacking`, as in
`SymplecticBallPacking.two_ball_obstruction_dim4`: `HasPacking 2 5 1 (fun _ => c)` says that five closed balls of
capacity `c` embed symplectically, with pairwise disjoint images, into the open ball of capacity `1`. -/
theorem five_ball_obstruction_dim4 (c : ℝ) (hc : 0 < c)
    (hp : HasPacking 2 5 1 (fun _ => c)) : c ≤ 2 / 5 := by
  sorry

end LefebvreVariations
