-- Prove2me | Theorems.Thm_MagicSquares_param_three_card
-- name    : MagicSquares.param_three_card
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-16T14:14:58.404311+00:00
-- url     : https://prove2.me/theorems/8063946a-dd43-4ff9-9107-f3e4d7cb040b
-- title:
--   Counting admissible MacMahon parameters for 3x3 squares
-- statement:
--   The number of admissible MacMahon parameter pairs for
--   line sum $3e$ is
--   $$\mathrm{paramCount}(e) \;=\; \#\{(a,c) \in \mathbb{N}^{2} : e \le a+c \le 3e,\;
--   a \le e+c,\; c \le e+a\} \;=\; 2e^{2} + 2e + 1 .$$
--
--   **Proof.** Substituting $p = a - e$ and $q = c - e$, the four inequalities read
--   $|p+q| \le e$ and $|p-q| \le e$, and since
--   $\max(|p+q|,|p-q|) = |p| + |q|$ this is exactly $|p| + |q| \le e$: the
--   $\ell_{1}$ ball of radius $e$ in $\mathbb{Z}^{2}$. On the sphere
--   $|p| + |q| = k$ there are $4k$ lattice points for $k \ge 1$ and one for $k = 0$,
--   so the ball has
--   $$1 + \sum_{k=1}^{e} 4k \;=\; 1 + 2e(e+1) \;=\; 2e^{2} + 2e + 1$$
--   points.
--
--   Equivalently one may sum over $a$: for fixed $a \in [0,2e]$ the admissible $c$
--   form the interval $[\,|a-e|,\ \min(a+e,\,3e-a)\,]$, which has $2a+1$ elements when
--   $a \le e$ and $4e-2a+1$ elements when $a \ge e$; summing gives
--   $(e+1)^{2} + e^{2} = 2e^{2} + 2e + 1$.
--
--   **Formalization Note** `paramCount e` is the cardinality of the finset
--   `paramSet e`, defined by filtering the box $[0,2e] \times [0,2e]$ — the bounds
--   $a, c \le 2e$ are implied by admissibility, so this is lossless.
-- source:
--   P. A. MacMahon, Combinatory Analysis (1915): $M_3(t) = \tfrac{2}{9}t^2 + \tfrac{2}{3}t + 1$ for $3 \mid t$.

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresParam3
open MagicSquares

namespace MagicSquares

theorem param_three_card (e : ℕ) :
    paramCount e = 2 * e ^ 2 + 2 * e + 1 := by sorry

end MagicSquares
