-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_real_bound_below6
-- name    : HlawkaSchatten.DiagonalCutoff.real_bound_below6
-- status  : Open
-- author  : @Nihal
-- created : 2026-10-28T01:18:24.065232+00:00
-- url     : https://prove2.me/theorems/dc148539-b500-4121-af35-e15ebc8c5c22
-- title:
--   The real coordinate Hlawka bound for $2 \le p \le 6$
-- statement:
--   For a real exponent $p$ and a vector $x \in \mathbb{R}^n$, the **coordinate norm** is
--
--   $$
--   N_p(x) = \Bigl(\sum_{i=1}^{n} |x_i|^p\Bigr)^{1/p} .
--   $$
--
--   For three vectors $x,y,z \in \mathbb{R}^n$, the **triple deficit** and the **pair-deficit sum** are
--
--   $$
--   \Delta_3 = N_p(x)+N_p(y)+N_p(z)-N_p(x+y+z),
--   \qquad
--   \Delta_2 = 2\bigl(N_p(x)+N_p(y)+N_p(z)\bigr) - N_p(x+y) - N_p(x+z) - N_p(y+z),
--   $$
--
--   and a real constant $C$ is *uniformly admissible* for $N_p$ when $\Delta_3 \le C\,\Delta_2$ for every triple in every finite dimension. For $t \in [1/2,2]$ put
--
--   $$
--   A_p(t) = (t^p+2)^{1/p}, \qquad
--   B_p(t) = \bigl(2|1-t|^p + 2^p\bigr)^{1/p},
--   \qquad
--   R_p(t) = \frac{3A_p(t) - 3^{1/p}|2-t|}{6A_p(t) - 3B_p(t)},
--   $$
--
--   $$
--   K_p = \sup_{t \in [1/2,2]} R_p(t).
--   $$
--
--   The quantity $K_p$ is the **cyclic constant**: the cyclic family $(-t,1,1)$, $(1,-t,1)$, $(1,1,-t)$ has all three singleton norms equal to $A_p(t)$, all three pairwise sums of norm $B_p(t)$ and total sum of norm $3^{1/p}|2-t|$, so its comparison ratio is $R_p(t)$. Because $2A_p(t)-B_p(t) > 0$ on the parameter range, every such triple has $\Delta_2 > 0$; hence no admissible constant can be smaller than $\sup_t R_p(t) = K_p$, and this statement is tight.
--
--   The theorem asserts that for every exponent in the compact range $2 \le p \le 6$ the coordinate norm on $\mathbb{R}^n$ is admissible with exactly this constant:
--
--   $$
--   \forall p \in [2,6],\ \forall n \in \mathbb{N},\ \forall x,y,z \in \mathbb{R}^n:
--   \qquad \Delta_3 \le K_p\,\Delta_2 ,
--   $$
--
--   again with no normalization or equal-norm hypothesis, and with the dimension allowed to be zero.
--
--   This interval is the part of the sharp real diagonal problem that remains open. Its structure is worth recording, since the three sub-intervals behave very differently. For $2 \le p \le \log 3/\log(3/2) \approx 2.7095$ the constant equals $1$, the statement is precisely Hlawka's classical inequality, and Hlawka's inequality is *known to fail* for $p$ above that threshold, so the constant genuinely exceeds $1$ from there on. At the other end, from $p \ge 4$ the dimension can be reduced to three, and the three-dimensional problem has been settled for $p \ge 6$; what remains in $[4,6)$ is the three-dimensional interval. The constants increase steeply across the interval, from $K_2 = 1$ through $K_3 \approx 1.093$ and $K_4 \approx 1.467$ to $K_6 \approx 2.305$.
-- source:
--   Remaining range of the sharp real diagonal Hlawka endpoint on Prove2Me (campaign sharp-diagonal-hlawka-constant, mission 'Sharp diagonal Hlawka constants: lower the cutoff to 2'); the constant is that of E. Esa, Hlawka-Schatten inequalities: sharp diagonal construction, https://github.com/savarin/hlawka-schatten/tree/79aa498bfcf7b22bd91d771fb32ec278e2d4704b ; cf. K. M. R. Audenaert and F. Kittaneh, Problems and Conjectures in Matrix and Operator Inequalities, arXiv:1201.5232, Problem 7.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff.real_bound_below6 :
    ∀ p : ℝ, 2 ≤ p → p ≤ 6 → ∀ n : ℕ,
      HasHlawkaConstant (lpNorm p : (Fin n → ℝ) → ℝ)
        (cyclicConstant p) := by sorry
