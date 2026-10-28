-- Prove2me | Theorems.Thm_HlawkaSchatten_LpThreshold_cyclicConstant_le_one_below
-- name    : HlawkaSchatten.LpThreshold.cyclicConstant_le_one_below
-- status  : Open
-- author  : @Nihal
-- created : 2026-10-28T01:36:33.461039+00:00
-- url     : https://prove2.me/theorems/3eb23cfd-ec81-44a6-97e8-72ad066274fe
-- title:
--   The cyclic constant equals one below the Hlawka threshold
-- statement:
--   For a real exponent $p$ and a parameter $t \in [1/2,2]$ put
--
--   $$
--   A_p(t) = \bigl(t^p + 2\bigr)^{1/p}, \qquad
--   B_p(t) = \bigl(2\,|1-t|^p + 2^p\bigr)^{1/p},
--   $$
--
--   and let the **cyclic constant** be
--
--   $$
--   K_p \;=\; \sup_{t \in [1/2,\,2]} \frac{3A_p(t) - 3^{1/p}|2-t|}{6A_p(t) - 3B_p(t)} .
--   $$
--
--   The quantity $K_p$ is the comparison ratio forced by the three real vectors $(-t,1,1)$, $(1,-t,1)$, $(1,1,-t)$ under the coordinate norm $N_p(x) = \bigl(\sum_i |x_i|^p\bigr)^{1/p}$: each of the three has norm $A_p(t)$, each pairwise sum has norm $B_p(t)$, and the total sum has norm $3^{1/p}|2-t|$.
--
--   The theorem asserts that below the **Hlawka threshold**
--
--   $$
--   p_0 = \frac{\log 3}{\log(3/2)} \approx 2.70951
--   $$
--
--   the cyclic constant is exactly one:
--
--   $$
--   2 \le p \le p_0 \quad\Longrightarrow\quad K_p \le 1 .
--   $$
--
--   Together with the companion bound $K_p \ge 1$ (obtained by evaluating the ratio at $t = 2$, where numerator and denominator both equal $3A_p(2)$), this pins $K_p = 1$ on $[2,p_0]$.
--
--   The threshold is not an artefact of the definition: it is exactly the exponent at which the cyclic family stops satisfying the classical Hlawka inequality with constant one. Concretely, at $t = 1$ the three vectors are $(-1,1,1)$, $(1,-1,1)$, $(1,1,-1)$, whose singleton norms are all $3^{1/p}$, whose pairwise sums all have norm $2$, and whose total sum has norm $3^{1/p}$; the classical inequality therefore reads $2\cdot 3^{1/p} \le 6\cdot 3^{1/p} - 6$, which is equivalent to $3^{1/p} \ge 3/2$, i.e. to $p \le p_0$. It is a theorem that Hlawka's inequality in $\ell_p$ fails for every $p > p_0$, so $p_0$ is the exact right endpoint of the range on which the constant can equal one.
--
--   The mathematical content is therefore that among all $t \in [1/2,2]$, the maximum of the cyclic ratio is attained at $t = 2$ precisely when $p \le p_0$; for $p$ above the threshold the maximum migrates into the interior of the interval and the constant becomes strictly larger than one. The statement is a scalar, one-parameter inequality — it involves no vectors, no dimension and no norm inequality, and it is independent of the analytic difficulty of Hlawka's inequality itself. That separation is its purpose: it isolates the computation of the constant from the proof that the constant is admissible.
-- source:
--   Scalar half of the low-exponent regime of the sharp diagonal Hlawka problem on Prove2Me (campaign sharp-diagonal-hlawka-constant); threshold exponent as in http://arxiv.org/abs/2407.03278 and E. Esa, Hlawka-Schatten inequalities: sharp diagonal construction, https://github.com/savarin/hlawka-schatten/tree/79aa498bfcf7b22bd91d771fb32ec278e2d4704b .

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.LpThreshold.cyclicConstant_le_one_below :
    ∀ p : ℝ, 2 ≤ p → p ≤ Real.log 3 / Real.log (3 / 2) → cyclicConstant p ≤ 1 := by sorry
