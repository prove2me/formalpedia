-- Prove2me | Theorems.Thm_MagicSquares_magic_three_param_sufficient
-- name    : MagicSquares.magic_three_param_sufficient
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-16T15:34:57.720881+00:00
-- url     : https://prove2.me/theorems/665c40f1-688c-4f40-aafb-1b8d82bbeb35
-- title:
--   The three-parameter array is a magic square of line sum 3e
-- statement:
--   **The parametrization is sound.** Let $e,a,c$ be nonnegative integers
--   satisfying the admissibility inequalities
--
--   $$
--   e \le a+c,\qquad a+c \le 3e,\qquad a \le e+c,\qquad c \le e+a ,
--   $$
--
--   and let $M(a,c)$ be the array
--
--   $$
--   \begin{pmatrix}
--   a & 3e-a-c & c\\
--   e+c-a & e & e+a-c\\
--   2e-c & a+c-e & 2e-a
--   \end{pmatrix} .
--   $$
--
--   Then $M(a,c)$ is a **magic square** of line sum $3e$: all three rows, all three
--   columns, and both main diagonals sum to $3e$.
--
--   The inequalities are exactly what makes the truncations in $\mathbb{N}$ harmless.
--   Row $0$ needs $a+c\le 3e$ so that $3e-a-c$ is not truncated; row $1$ needs
--   $a\le e+c$ and $c\le e+a$ for the same reason on $e+c-a$ and $e+a-c$; row $2$
--   needs $c\le 2e$, $a+c\ge e$ and $a\le 2e$, and the bounds $a,c\le 2e$ follow
--   from the hypotheses by adding $a\le e+c$ to $a+c\le 3e$ (giving $2a\le 4e$) and
--   symmetrically. The columns and diagonals are then pure cancellation.
--
--   Together with the companion *necessary* direction this shows that the map
--   $(a,c)\mapsto M(a,c)$ is a parametrization of the order-three magic squares of
--   line sum $3e$.
--
--   **Formalization Note** `mkMagic3` is defined over $\mathbb{N}$ with truncated
--   subtraction, so every line identity is proved by `omega` after discharging the
--   relevant non-truncation side condition. The statement is otherwise unconditional
--   apart from admissibility.
-- source:
--   Beck, Cohen, Cuomo & Gribelyuk, The number of ``magic'' squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707--717; arXiv:math/0201013v3. G. Xin, Constructing all magic squares of order three, Discrete Math. 308 (2008); arXiv:math/0610771.

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresParam3

namespace MagicSquares

theorem magic_three_param_sufficient (e a c : ℕ) (h : IsParam3 e a c) :
    IsMagic (mkMagic3 e a c) (3 * e) := by sorry

end MagicSquares
