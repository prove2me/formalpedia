-- Prove2me | Theorems.Thm_LefebvreVariations_seven_ball_obstruction_dim4
-- name    : LefebvreVariations.seven_ball_obstruction_dim4
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:31:30.126227+00:00
-- url     : https://prove2.me/theorems/797f4efd-b8c5-417b-b038-69c9bd5dd816
-- title:
--   Lefebvre's variations, No. 173 — on a theme by Gromov: seven equal balls do not pack the four-dimensional ball beyond capacity three eighths
-- statement:
--   Let seven balls of capacity $c>0$ be symplectically embedded in the open ball of capacity $1$ of $\mathbb C^2$ with pairwise disjoint images: that is, there are symplectic embeddings $f_1,\dots,f_{7}$ of neighbourhoods of the closed balls $B(c)=\{z:\pi|z|^2\le c\}$ with $f_i\bigl(B(c)\bigr)\subset\{\pi|z|^2<1\}$ and $f_i\bigl(B(c)\bigr)\cap f_j\bigl(B(c)\bigr)=\emptyset$ for $i\ne j$. Then
--   $$
--   c\;\le\;\frac{3}{8}.
--   $$
--   Equivalently, at most the fraction $7\left(\frac{3}{8}\right)^2=\frac{63}{64}$ of the volume of the ball can be filled by seven equal balls. The bound comes from the exceptional class $3L-2E_1-E_2-\cdots-E_7$ of the blow-up of $\mathbb{CP}^2$ at 7 points, which gives the inequality $3\ge 2c+6c=8c$; Gromov's two-ball inequality $a+b\le1$ is the analogous statement for two balls.
--
--   **Formalization Note** The statement uses the platform definition `OAI.HigherDimensionalBallPacking.HasPacking` of `Def_BallPacking`, exactly as in `SymplecticBallPacking.two_ball_obstruction_dim4`: `HasPacking 2 7 1 (fun _ => c)` says that 7 closed balls of capacity `c` (`capacity z = π ∑ |z_j|²`) embed symplectically (`SymplecticOn`: smooth embeddings of open neighbourhoods preserving the standard form), with pairwise disjoint images, into the open ball of capacity `1`. The hypothesis `0 < c` keeps the balls non-degenerate.
--
--   **Why this is a variation.** This varies the open platform problem `SymplecticBallPacking.two_ball_obstruction_dim4`, Gromov's two-ball inequality $a+b\le1$ for symplectic packings of the four-dimensional ball. It plays the same obstruction for seven equal balls, where the exceptional class $3L-2E_1-E_2-\cdots-E_7$ of the blow-up of the projective plane gives the sharp bound $c\le 3/8$, with the parent's own `HasPacking` definition. It is the case in the packing-number table that follows the five- and six-ball cases.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   D. McDuff and L. Polterovich, Symplectic packings and algebraic geometry, Invent. Math. 115 (1994) 405-434; M. Gromov, Pseudo holomorphic curves in symplectic manifolds, Invent. Math. 82 (1985) 307-347 (page numbers not verified). Origin of this statement: the seven-ball case of the symplectic packing obstruction in dimension four (platform family SymplecticBallPacking), the next sizes after SymplecticBallPacking.two_ball_obstruction_dim4 (Gromov's two-ball inequality a + b <= 1). Numerical check of the data: the class 3L - 2E1 - E2 - ... - E7 has self-intersection -1 and first Chern number 1, and 7 * (3/8)^2 = 63/64, the known packing number of 7 equal balls.
--    Verified by web search on 26 Nov 2026: the existence and title of McDuff-Polterovich 1994 (MaRDI record) and the packing-number table v_2..v_9 = 1/2, 3/4, 1, 4/5, 24/25, 63/64, 288/289, 1 (P. Biran, survey, https://www.math.uni-bielefeld.de/~rehmann/ECM/cdrom/3ecm/pdfs/pant3/biran.pdf, attributing it to McDuff-Polterovich). The exceptional-class description is cited from memory.

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_SymplecticBallPacking

set_option autoImplicit false

open scoped ContDiff

namespace LefebvreVariations

open OAI.HigherDimensionalBallPacking
open Set

/-- **Seven equal balls do not pack `B⁴(1)` beyond capacity `3/8`.** If seven disjoint symplectic images of
the closed balls of capacity `c` sit inside the open ball of capacity `1` in `ℂ²`, then `c ≤ 3/8` (so at most
`7 (3/8)² = 63/64` of the volume is filled). Obstruction from the exceptional class `3L - 2E₁ - E₂ - … - E₇` of
the blow-up of `ℂP²` at seven points, which gives `2c + 6c ≤ 3` (McDuff–Polterovich, Invent. Math. 115
(1994) 405–434, cited from memory).

**Formalization Note.** Uses the platform definitions `HasPacking` of `Def_BallPacking`, as in
`SymplecticBallPacking.two_ball_obstruction_dim4`: `HasPacking 2 7 1 (fun _ => c)` says that seven closed balls of
capacity `c` embed symplectically, with pairwise disjoint images, into the open ball of capacity `1`. -/
theorem seven_ball_obstruction_dim4 (c : ℝ) (hc : 0 < c)
    (hp : HasPacking 2 7 1 (fun _ => c)) : c ≤ 3 / 8 := by
  sorry

end LefebvreVariations
