-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_real_three_threshold_to_four
-- name    : HlawkaSchatten.DiagonalCutoff4.real_three_threshold_to_four
-- status  : Open
-- author  : @Nihal
-- created : 2026-10-28T01:36:35.640833+00:00
-- url     : https://prove2.me/theorems/f2e75c6b-eda8-47e1-8d1f-64207f559bc6
-- title:
--   The real three-dimensional Hlawka interval $[\log 3/\log(3/2),\,4]$
-- statement:
--   For a real exponent $p$ and vectors $x,y,z \in \mathbb{R}^3$ the **coordinate norm** is
--
--   $$
--   N_p(x) = \Bigl(\sum_{i=1}^{3} |x_i|^p\Bigr)^{1/p},
--   $$
--
--   and the **triple deficit** and **pair-deficit sum** are
--
--   $$
--   \Delta_3 = N_p(x)+N_p(y)+N_p(z)-N_p(x+y+z),
--   \qquad
--   \Delta_2 = 2\bigl(N_p(x)+N_p(y)+N_p(z)\bigr) - N_p(x+y)-N_p(x+z)-N_p(y+z).
--   $$
--
--   For $t \in [1/2,2]$ put $A_p(t) = (t^p+2)^{1/p}$ and $B_p(t) = \bigl(2|1-t|^p+2^p\bigr)^{1/p}$, and let
--
--   $$
--   K_p \;=\; \sup_{t \in [1/2,2]} \frac{3A_p(t) - 3^{1/p}|2-t|}{6A_p(t) - 3B_p(t)}
--   $$
--
--   be the **cyclic constant**, i.e. the comparison ratio forced by the cyclic family $(-t,1,1),(1,-t,1),(1,1,-t)$.
--
--   The theorem asserts the three-dimensional real Hlawka bound for exponents strictly above the Hlawka threshold $p_0 = \log 3/\log(3/2) \approx 2.70951$ and up to $4$:
--
--   $$
--   \forall p \in [p_0,\,4],\ \forall x,y,z \in \mathbb{R}^3:\qquad
--   \Delta_3 \;\le\; K_p\,\Delta_2 .
--   $$
--
--   No normalization, equal-norm or nonvanishing hypothesis is imposed, and the statement is made in dimension three only; the passage to arbitrary finite dimension is a separate theorem.
--
--   This is the part of the low-exponent range where the problem is no longer classical. Below $p_0$ the constant equals $1$ and the assertion reduces to Hlawka's inequality; it is known that Hlawka's inequality fails in $\ell_p$ for every $p > p_0$, so throughout the present interval the constant genuinely exceeds one, rising from $K_{p_0} = 1$ to $K_4 \approx 1.46711$. The left endpoint is included so that the interval joins continuously to the classical range: at $p = p_0$ the statement is still Hlawka's inequality, since $K_{p_0} = 1$.
--
--   The statement is sharp rather than merely sufficient. Because $2A_p(t) - B_p(t)$ is strictly positive on the parameter range, the pair-deficit sum of every cyclic triple is positive, so each cyclic triple yields a legitimate lower bound $\sup_t R_p(t) = K_p$ for any admissible constant. The target constant is thus the best possible, and a proof of the statement cannot proceed by any argument that leaves slack in the constant.
--
--   Structurally the interval is the genuinely new portion of the compact range below the established cutoff: uniform bounds are known for complex exponents $p \ge 6$ and hence for real exponents $p \ge 6$, and the three-dimensional real bound is known for $p \ge 6$ from the windowed confinement analysis and for $p \ge 8$ from the diagonal construction. What remains below $6$ is the three-dimensional interval $[2,6]$, and the present statement is its upper part $[p_0,4]$, the part above the classical Hlawka threshold.
-- source:
--   Middle piece of the sharp real diagonal Hlawka problem on Prove2Me (campaign sharp-diagonal-hlawka-constant, mission 'Sharp diagonal Hlawka constants: lower the cutoff to 2'); constant as in E. Esa, Hlawka-Schatten inequalities: sharp diagonal construction, https://github.com/savarin/hlawka-schatten/tree/79aa498bfcf7b22bd91d771fb32ec278e2d4704b ; threshold exponent as in http://arxiv.org/abs/2407.03278 .

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.real_three_threshold_to_four :
    ∀ p : ℝ, Real.log 3 / Real.log (3 / 2) ≤ p → p ≤ 4 →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
