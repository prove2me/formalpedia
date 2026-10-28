-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_cyclicConstant_ge_one
-- name    : HlawkaSchatten.DiagonalConstruction.cyclicConstant_ge_one
-- status  : Proved
-- author  : @Nihal
-- created : 2026-10-28T01:33:26.331639+00:00
-- url     : https://prove2.me/theorems/5517b548-6d0d-415c-8a24-0f3ebeb59c31
-- title:
--   The cyclic constant is at least one
-- statement:
--   For a real exponent $p > 1$ and a parameter $t \in [1/2, 2]$, put
--
--   $$
--   A_p(t) = \bigl(t^p + 2\bigr)^{1/p}, \qquad
--   B_p(t) = \bigl(2\,|1-t|^p + 2^p\bigr)^{1/p},
--   $$
--
--   and define the **cyclic ratio**
--
--   $$
--   R_p(t) \;=\; \frac{3A_p(t) - 3^{1/p}\,|2-t|}{6A_p(t) - 3B_p(t)} .
--   $$
--
--   The denominator is strictly positive on the parameter range, the function $t \mapsto R_p(t)$ is continuous there, and the interval $[1/2,2]$ is compact, so $R_p$ attains a maximum. The **cyclic constant** is that maximum,
--
--   $$
--   K_p \;=\; \sup_{t \in [1/2,\,2]} R_p(t).
--   $$
--
--   Geometrically, $R_p(t)$ is the ratio of the triple deficit to the pair-deficit sum of the three real vectors $(-t,1,1)$, $(1,-t,1)$, $(1,1,-t)$ under the coordinate norm $N_p(x) = \bigl(\sum_i |x_i|^p\bigr)^{1/p}$; the constant $K_p$ is the comparison ratio this one-parameter family forces, and it is the sharp constant in the diagonal Hlawka problem.
--
--   The theorem asserts a universal lower bound for this supremum:
--
--   $$
--   K_p \;\ge\; 1 \qquad \text{for every } p > 1 .
--   $$
--
--   The proof is a single evaluation: at the right endpoint $t = 2$ the two auxiliary quantities coincide, $B_p(2) = A_p(2)$, because $|1-2| = 1$ and $|2-2| = 0$, so both the numerator and the denominator of $R_p(2)$ equal $3A_p(2)$ and $R_p(2) = 1$. Since $2$ lies in the parameter interval, a maximum of $R_p$ over that interval is at least the value at $2$, hence $K_p \ge 1$.
--
--   The bound is not an artefact of the endpoint: it is exactly what makes the normalization hypotheses in the downstream reduction and curvature criteria satisfiable, so the statement is recorded for every $p > 1$ even though the extremal ratio can dip below $1$ strictly inside the interval when $p$ is small.
-- source:
--   Elementary lower bound for the sharp cyclic constant of the diagonal Hlawka construction on Prove2Me (campaign sharp-diagonal-hlawka-constant); constant as in E. Esa, Hlawka-Schatten inequalities: sharp diagonal construction, https://github.com/savarin/hlawka-schatten/tree/79aa498bfcf7b22bd91d771fb32ec278e2d4704b .

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalConstruction.cyclicConstant_ge_one {p : ℝ} (hp : 1 < p) :
    1 ≤ cyclicConstant p := by sorry
