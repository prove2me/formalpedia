-- Prove2me | Theorems.Thm_LefebvreVariations_four_ball_full_packing_dim4
-- name    : LefebvreVariations.four_ball_full_packing_dim4
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:32:53.203811+00:00
-- url     : https://prove2.me/theorems/837e4301-d57d-4576-8d83-22c1c6cdede7
-- title:
--   Lefebvre's variations, No. 213 — on a theme by Biran: four equal balls fill the four-dimensional ball up to any fraction by symplectic packing
-- statement:
--   For every $\varepsilon\in(0,1)$ there is a number $c>0$ such that four balls of capacity $c$ can be symplectically embedded, with pairwise disjoint images, in the open ball of capacity $1$ of $\mathbb C^2$, and
--   $$
--   4\,c^{2}\;>\;1-\varepsilon .
--   $$
--   That is, there are symplectic embeddings $f_1,\dots,f_4$ of neighbourhoods of the closed balls $B(c)=\{z:\pi|z|^2\le c\}$ with $f_i\bigl(B(c)\bigr)\subset\{\pi|z|^2<1\}$ and $f_i\bigl(B(c)\bigr)\cap f_j\bigl(B(c)\bigr)=\emptyset$ for $i\ne j$, filling more than $1-\varepsilon$ of the volume. In other words, the symplectic packing number of four equal balls is $1$: no obstruction other than volume remains.
--
--   **Formalization Note** The statement has the same conclusion as `SymplecticBallPacking.full_packing_dim4` but with `k = 4` instead of `k ≥ 9`: `HasPacking 2 4 1 (fun _ => c)` and `(4 : ℝ) * c ^ 2 > 1 - ε`, with `HasPacking` the platform definition of `Def_BallPacking` (smooth symplectic embeddings of open neighbourhoods of closed balls of capacity `c` into the open ball of capacity `1`, with pairwise disjoint images).
--
--   **Why this is a variation.** This varies the open platform problem `SymplecticBallPacking.full_packing_dim4`, full symplectic packing of the four-dimensional ball by $k\ge9$ equal balls (Biran). It plays the same statement at $k=4$, the small case where a full packing is also possible (the packing number is $1$ although $k=2,3,5,\dots,8$ have obstructions), with the parent's own `HasPacking` definition. It is a first nontrivial instance of the full-packing question below the platform's range $k\ge9$.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   D. McDuff and L. Polterovich, Symplectic packings and algebraic geometry, Invent. Math. 115 (1994) 405-434 (packing numbers p_1 = 1, p_2 = 1/2, p_3 = 3/4, p_4 = 1, p_5 = 20/25, ..., and p_k = 1 for k >= 9 in the later work of Biran, Invent. Math. 136 (1999) 123-155); M. Gromov, Pseudo holomorphic curves in symplectic manifolds, Invent. Math. 82 (1985) 307-347 (page numbers not verified). Origin of this statement: the case k = 4 of the full-packing question in dimension four (platform theorem SymplecticBallPacking.full_packing_dim4 has k >= 9).
--    Verified by web search on 26 Nov 2026: the existence and title of McDuff-Polterovich 1994 (MaRDI record) and the packing-number table v_2..v_9 = 1/2, 3/4, 1, 4/5, 24/25, 63/64, 288/289, 1 (P. Biran, survey, https://www.math.uni-bielefeld.de/~rehmann/ECM/cdrom/3ecm/pdfs/pant3/biran.pdf, attributing it to McDuff-Polterovich). The exceptional-class description is cited from memory.

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_SymplecticBallPacking

set_option autoImplicit false

open scoped ContDiff

namespace LefebvreVariations

open OAI.HigherDimensionalBallPacking
open Set

/-- **Four equal balls fill `B⁴(1)` up to any prescribed fraction.** For every `ε ∈ (0, 1)` there is `c > 0`
such that four disjoint symplectic images of the closed balls of capacity `c` sit inside the open ball of
capacity `1` in `ℂ²` and `4 c² > 1 - ε`; the packing number of four equal balls is `1`, the first case
(after the trivial one ball) in which the volume constraint is the only one (McDuff–Polterovich,
Invent. Math. 115 (1994) 405–434; Biran, Geom. Funct. Anal. 7 (1997) 420–437; both cited from memory).

**Formalization Note.** Same conclusion as `SymplecticBallPacking.full_packing_dim4` with `k = 4` instead of
`k ≥ 9`: `HasPacking 2 4 1 (fun _ => c)` and `(4 : ℝ) * c ^ 2 > 1 - ε`. -/
theorem four_ball_full_packing_dim4 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ c : ℝ, 0 < c ∧ HasPacking 2 4 1 (fun _ => c) ∧ (4 : ℝ) * c ^ 2 > 1 - ε := by
  sorry

end LefebvreVariations
