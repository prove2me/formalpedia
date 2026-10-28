-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_two_to_four
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_two_to_four
-- status  : Open
-- author  : @Nihal
-- created : 2026-10-28T01:34:26.243572+00:00
-- url     : https://prove2.me/theorems/643fc6a4-ae8f-4697-8d82-9bf42d7c1123
-- title:
--   The real three-dimensional Hlawka interval $[2,4]$
-- statement:
--   For a real exponent $p$ and a vector $x \in \mathbb{R}^n$ the **coordinate norm** is
--
--   $$
--   N_p(x) = \Bigl(\sum_{i=1}^{n} |x_i|^p\Bigr)^{1/p},
--   $$
--
--   and for three vectors $x,y,z \in \mathbb{R}^n$ the **triple deficit** and the **pair-deficit sum** are
--
--   $$
--   \Delta_3 = N_p(x)+N_p(y)+N_p(z)-N_p(x+y+z),
--   \qquad
--   \Delta_2 = 2\bigl(N_p(x)+N_p(y)+N_p(z)\bigr) - N_p(x+y)-N_p(x+z)-N_p(y+z).
--   $$
--
--   A constant $C$ is *admissible* for $N_p$ when $\Delta_3 \le C\,\Delta_2$ for every triple. For $t \in [1/2,2]$ let
--
--   $$
--   A_p(t) = (t^p+2)^{1/p}, \qquad B_p(t) = \bigl(2|1-t|^p+2^p\bigr)^{1/p},
--   $$
--
--   and let the **cyclic constant** be
--
--   $$
--   K_p = \sup_{t \in [1/2,2]} \frac{3A_p(t) - 3^{1/p}|2-t|}{6A_p(t) - 3B_p(t)} .
--   $$
--
--   Geometrically $K_p$ is the comparison ratio forced by the three real vectors $(-t,1,1)$, $(1,-t,1)$, $(1,1,-t)$: each has norm $A_p(t)$, each pairwise sum has norm $B_p(t)$, and the total sum has norm $3^{1/p}|2-t|$.
--
--   The theorem asserts that in **three real dimensions** the coordinate norm is admissible with the cyclic constant throughout the range $2 \le p \le 4$:
--
--   $$
--   \forall p \in [2,4],\ \forall x,y,z \in \mathbb{R}^3:\qquad \Delta_3 \;\le\; K_p\,\Delta_2 .
--   $$
--
--   No normalization, equal-norm or nonvanishing hypothesis is imposed, and the statement is made only in dimension three — the reduction from arbitrary finite dimension to three real coordinates is a separate, already available theorem.
--
--   Three comments on the role of this range. First, for $2 \le p \le \log 3/\log(3/2) \approx 2.7095$ the constant equals $1$, so there the assertion is precisely Hlawka's classical inequality; it is known that Hlawka's inequality fails for exponents above that threshold, so the constant genuinely exceeds $1$ from there onwards and this part of the range is not classical Hlawka. Second, at the left endpoint $p = 2$ the norm is Euclidean and the assertion is Hlawka's inequality in a Hilbert space, which holds with $C = 1 = K_2$; at the right endpoint $p = 4$ the constant is $K_4 \approx 1.46711$. Third, the statement is sharp and not merely sufficient: because $2A_p(t) - B_p(t)$ stays strictly positive on the parameter range, the pair-deficit sum of each cyclic triple is positive, so every admissible constant is at least $\sup_t R_p(t) = K_p$; the target constant is therefore the best possible one.
--
--   The interval is the part of the sharp diagonal problem that lies strictly below the established cutoffs: uniform bounds for all finite dimensions are known for complex exponents $p \ge 6$ and hence, by the real–complex transfer, for real exponents $p \ge 6$, while the sharp constant in dimension three is known for $p \ge 6$ from the windowed confinement analysis covering $[6,8]$ and for $p \ge 8$ from the diagonal construction. What the present statement isolates is the remaining compact three-dimensional interval $[2,4]$.
-- source:
--   Complement of HlawkaSchatten.DiagonalCutoff4.real_three_four_to_six in the sharp real diagonal Hlawka problem on Prove2Me (campaign sharp-diagonal-hlawka-constant, mission 'Sharp diagonal Hlawka constants: lower the cutoff to 2'); constant as in E. Esa, Hlawka-Schatten inequalities: sharp diagonal construction, https://github.com/savarin/hlawka-schatten/tree/79aa498bfcf7b22bd91d771fb32ec278e2d4704b ; threshold exponent log 3 / log(3/2) as in http://arxiv.org/abs/2407.03278 .

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.real_three_two_to_four :
    ∀ p : ℝ, 2 ≤ p → p ≤ 4 →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
