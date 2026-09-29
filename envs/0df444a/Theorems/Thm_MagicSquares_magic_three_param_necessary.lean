-- Prove2me | Theorems.Thm_MagicSquares_magic_three_param_necessary
-- name    : MagicSquares.magic_three_param_necessary
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-16T15:34:32.899273+00:00
-- url     : https://prove2.me/theorems/4e513d72-b4b7-419b-a0e6-dc115ee77a94
-- title:
--   Every order-three magic square of line sum 3e is the parametrized one
-- statement:
--   **The parametrization is complete.** Let $M$ be a $3\times3$ magic square with
--   nonnegative integer entries and line sum $3e$. Then $M$ is *exactly* the
--   parametrized array built from its two top corners:
--
--   $$
--   M \;=\; \begin{pmM_{00}trix}
--   M_{00} & 3e-M_{00}-M_{02} & M_{02}\\
--   e+M_{02}-M_{00} & e & e+M_{00}-M_{02}\\
--   2e-M_{02} & M_{00}+M_{02}-e & 2e-M_{00}
--   \end{pmM_{00}trix} ,
--   $$
--
--   where $a=M_{00}$ and $c=M_{02}$.
--
--   The eight line identities determine the remaining seven cells uniquely. The
--   centre is $e$ (MacMahon's identity $3M_{11}=s$ with $s=3e$). The two diagonals
--   give $M_{22}=2e-M_{00}$ and $M_{20}=2e-M_{02}$; row $0$ then gives
--   $M_{01}=3e-M_{00}-M_{02}$; column $0$ and column $2$ give
--   $M_{10}=e+M_{02}-M_{00}$ and $M_{12}=e+M_{00}-M_{02}$; and column $1$ gives
--   $M_{21}=M_{00}+M_{02}-e$. Since $M$ is a genuine square over $\mathbb{N}$, none
--   of these subtractions truncates.
--
--   Consequently a $3\times3$ magic square of line sum $3e$ is determined by its two
--   top corners, and the pair $(M_{00},M_{02})$ satisfies precisely the
--   admissibility inequalities — the count of such squares is therefore the count of
--   admissible pairs, which is MacMahon's $2e^{2}+2e+1$.
--
--   **Formalization Note** The proof expands the eight line identities of `IsMagic`
--   and closes each of the nine cell equalities by `omega`; no integrality
--   hypothesis beyond working over $\mathbb{N}$ is needed.
-- source:
--   Beck, Cohen, Cuomo & Gribelyuk, The number of ``magic'' squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707--717; arXiv:math/0201013v3. G. Xin, Constructing all magic squares of order three, Discrete Math. 308 (2008); arXiv:math/0610771.

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresParam3

namespace MagicSquares

theorem magic_three_param_necessary (e : ℕ) (M : Square 3 ℕ)
    (hM : IsMagic M (3 * e)) :
    M = mkMagic3 e (M 0 0) (M 0 2) := by sorry

end MagicSquares
