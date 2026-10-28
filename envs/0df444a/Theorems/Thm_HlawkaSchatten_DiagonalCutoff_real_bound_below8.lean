-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_real_bound_below8
-- name    : HlawkaSchatten.DiagonalCutoff.real_bound_below8
-- status  : Open
-- author  : @Nihal
-- created : 2026-10-28T01:11:55.880714+00:00
-- url     : https://prove2.me/theorems/a4746a21-4f99-4b78-a4ed-fe1d33c21eee
-- title:
--   The real coordinate Hlawka bound for $2 \le p \le 8$
-- statement:
--   For a real exponent $p$ and a vector $x \in \mathbb{R}^n$, the **coordinate norm** is
--
--   $$
--   N_p(x) = \Bigl(\sum_{i=1}^{n} |x_i|^p\Bigr)^{1/p} .
--   $$
--
--   For three vectors $x,y,z \in \mathbb{R}^n$ the **triple deficit** and the **pair-deficit sum** are
--
--   $$
--   \Delta_3 = N_p(x)+N_p(y)+N_p(z)-N_p(x+y+z),
--   $$
--
--   $$
--   \Delta_2 = 2\bigl(N_p(x)+N_p(y)+N_p(z)\bigr)
--    - N_p(x+y) - N_p(x+z) - N_p(y+z).
--   $$
--
--   A real constant $C$ is *uniformly admissible* for $N_p$ when $\Delta_3 \le C\,\Delta_2$ for every triple in every finite dimension. For $t \in [1/2,2]$ put
--
--   $$
--   A_p(t) = (t^p+2)^{1/p}, \qquad
--   B_p(t) = \bigl(2|1-t|^p + 2^p\bigr)^{1/p},
--   $$
--
--   $$
--   R_p(t) = \frac{3A_p(t) - 3^{1/p}|2-t|}{6A_p(t) - 3B_p(t)},
--   \qquad K_p = \sup_{t \in [1/2,2]} R_p(t).
--   $$
--
--   The quantity $K_p$ is the **cyclic constant**, the comparison ratio forced by the cyclic family $(-t,1,1)$, $(1,-t,1)$, $(1,1,-t)$ of real three-vectors. For this family all three singleton norms equal $A_p(t)$, all three pairwise sums have norm $B_p(t)$, and the total sum has norm $3^{1/p}|2-t|$; moreover $2A_p(t) - B_p(t) > 0$ throughout the parameter range, so every such triple has $\Delta_2 > 0$. Consequently $K_p$ is a *lower* bound for the sharp real constant as well: no uniform constant smaller than $K_p$ can be admissible.
--
--   The theorem asserts that for every real exponent in the compact range $2 \le p \le 8$ the coordinate norm on $\mathbb{R}^n$ is admissible with precisely this constant:
--
--   $$
--   \forall p \in [2,8],\ \forall n \in \mathbb{N},\ \forall x,y,z \in \mathbb{R}^n:
--   \qquad \Delta_3 \le K_p\,\Delta_2 .
--   $$
--
--   No equal-norm, normalization or nonvanishing hypothesis is imposed, and the dimension may be zero. The statement asserts admissibility only: it makes no leastness claim.
--
--   Because $K_p$ is the sharp constant, this is a tight statement, not one with numerical room to spare. The endpoints are known: at $p = 2$ the norm is Euclidean, $K_2 = 1$, and the assertion is Hlawka's classical inequality, while for $p \ge 8$ the bound is established. The interval $2 < p < 8$ is the part of the sharp real diagonal problem that remains open; it is the range in which classical Hlawka's inequality ($C = 1$) is no longer sufficient, since $K_p$ first exceeds $1$ near $p \approx 2.7$.
-- source:
--   Remaining range of the sharp real diagonal Hlawka endpoint on Prove2Me (campaign sharp-diagonal-hlawka-constant, mission 'Sharp diagonal Hlawka constants: lower the cutoff to 2'); the constant is that of E. Esa, Hlawka-Schatten inequalities: sharp diagonal construction, https://github.com/savarin/hlawka-schatten/tree/79aa498bfcf7b22bd91d771fb32ec278e2d4704b ; cf. K. M. R. Audenaert and F. Kittaneh, Problems and Conjectures in Matrix and Operator Inequalities, arXiv:1201.5232, Problem 7.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff.real_bound_below8 :
    ∀ p : ℝ, 2 ≤ p → p ≤ 8 → ∀ n : ℕ,
      HasHlawkaConstant (lpNorm p : (Fin n → ℝ) → ℝ)
        (cyclicConstant p) := by sorry
