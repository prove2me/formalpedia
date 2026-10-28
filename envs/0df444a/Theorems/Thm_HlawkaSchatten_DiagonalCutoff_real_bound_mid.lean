-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_real_bound_mid
-- name    : HlawkaSchatten.DiagonalCutoff.real_bound_mid
-- status  : Open
-- author  : @Nihal
-- created : 2026-10-28T01:02:03.520444+00:00
-- url     : https://prove2.me/theorems/c88417e5-f952-4084-91a9-e22306de22c0
-- title:
--   The real coordinate Hlawka bound for $2 \le p \le 16$
-- statement:
--   For a real exponent $p$ with $2 \le p \le 16$ and a vector $x \in \mathbb{R}^n$, the
--   **coordinate norm** is
--
--   $$
--   N_p(x) = \Bigl(\sum_{i=1}^{n} |x_i|^p\Bigr)^{1/p},
--   $$
--
--   and for three vectors $x,y,z \in \mathbb{R}^n$ the **triple deficit** and the
--   **pair-deficit sum** are
--
--   $$
--   \Delta_3 = N_p(x)+N_p(y)+N_p(z)-N_p(x+y+z),
--   $$
--
--   $$
--   \Delta_2 = 2\bigl(N_p(x)+N_p(y)+N_p(z)\bigr)
--   -N_p(x+y)-N_p(x+z)-N_p(y+z).
--   $$
--
--   A real constant $C$ is uniformly admissible when $\Delta_3 \le C\,\Delta_2$ holds for
--   every triple in every finite dimension. For $t \in [1/2,2]$ define
--
--   $$
--   A_p(t) = (t^p+2)^{1/p}, \qquad
--   B_p(t) = \bigl(2|1-t|^p + 2^p\bigr)^{1/p},
--   $$
--
--   $$
--   R_p(t) = \frac{3A_p(t) - 3^{1/p}|2-t|}{6A_p(t) - 3B_p(t)},
--   \qquad K_p = \sup_{t\in[1/2,2]} R_p(t),
--   $$
--
--   so that $K_p$ is the foundation's `cyclicConstant`, the constant forced by the
--   cyclic family $(-t,1,1),(1,-t,1),(1,1,-t)$.
--
--   The theorem asserts that for every $p$ in the compact range $2 \le p \le 16$ the
--   coordinate norm $N_p$ on $\mathbb{R}^n$ is admissible with the constant $K_p$:
--
--   $$
--   \forall p \in [2,16],\ \forall n \in \mathbb{N},\ \forall x,y,z \in \mathbb{R}^n,
--   \qquad \Delta_3 \le K_p\,\Delta_2 .
--   $$
--
--   There is no equal-norm, normalization or nonzero restriction, and the finite
--   dimension may be zero. The statement asserts admissibility only; it makes no
--   leastness claim about $K_p$. It is the range restriction of the campaign endpoint
--   for $p \ge 2$ that remains open after the accepted bound for every $p \ge 16$.
-- source:
--   Range restriction of the campaign endpoint theorem HlawkaSchatten.DiagonalCutoff.real_bound2 (Prove2Me, sharp diagonal Hlawka campaign, https://prove2.me/campaigns/sharp-diagonal-hlawka-constant). Construction: E. Esa, Hlawka-Schatten inequalities: sharp diagonal construction, https://github.com/savarin/hlawka-schatten/tree/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction . See also K. M. R. Audenaert and F. Kittaneh, Problems and Conjectures in Matrix and Operator Inequalities, arXiv:1201.5232, Problem 7.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff.real_bound_mid :
    ∀ p : ℝ, 2 ≤ p → p ≤ 16 → ∀ n : ℕ,
      HasHlawkaConstant (lpNorm p : (Fin n → ℝ) → ℝ)
        (cyclicConstant p) := by sorry
