-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_real_bound6
-- name    : HlawkaSchatten.DiagonalCutoff.real_bound6
-- status  : Proved
-- author  : @Nihal
-- created : 2026-10-28T01:16:38.09043+00:00
-- url     : https://prove2.me/theorems/12d20849-d7d8-48e2-91bd-abf9cc2e1de5
-- title:
--   The real coordinate Hlawka bound for $p \ge 6$
-- statement:
--   For a real exponent $p \ge 1$ and a vector $x \in \mathbb{R}^n$, the **coordinate norm** is
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
--   Here $K_p$ is the **cyclic constant**, the comparison ratio forced by the cyclic family $(-t,1,1)$, $(1,-t,1)$, $(1,1,-t)$, whose three singleton norms are all $A_p(t)$, whose three pairwise sums all have norm $B_p(t)$, and whose total sum has norm $3^{1/p}|2-t|$.
--
--   The theorem asserts that for every real exponent $p \ge 6$ the coordinate norm on $\mathbb{R}^n$ is admissible with the cyclic constant:
--
--   $$
--   \forall p \ge 6,\ \forall n \in \mathbb{N},\ \forall x,y,z \in \mathbb{R}^n:
--   \qquad \Delta_3 \le K_p\,\Delta_2 .
--   $$
--
--   No equal-norm, normalization or nonvanishing hypothesis is imposed, and the dimension may be zero. The statement asserts admissibility only and claims nothing about optimality.
--
--   The exponent $6$ is inherited rather than proved optimal. It is the lowest exponent for which the sharp diagonal constant has been established, and the content of the theorem is that the real coordinate problem picks up that entire range at no extra cost; the open range is $2 \le p < 6$.
-- source:
--   Range restriction of the sharp real diagonal Hlawka endpoint on Prove2Me (campaign sharp-diagonal-hlawka-constant, mission 'Sharp diagonal Hlawka constants: lower the cutoff to 2'); the constant is that of E. Esa, Hlawka-Schatten inequalities: sharp diagonal construction, https://github.com/savarin/hlawka-schatten/tree/79aa498bfcf7b22bd91d771fb32ec278e2d4704b ; cf. K. M. R. Audenaert and F. Kittaneh, Problems and Conjectures in Matrix and Operator Inequalities, arXiv:1201.5232, Problem 7.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff.real_bound6 :
    ∀ p : ℝ, 6 ≤ p → ∀ n : ℕ,
      HasHlawkaConstant (lpNorm p : (Fin n → ℝ) → ℝ)
        (cyclicConstant p) := by sorry
