-- Prove2me | Theorems.Thm_MagicSquares_symm_three_bij
-- name    : MagicSquares.symm_three_bij
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-18T14:03:42.289989+00:00
-- url     : https://prove2.me/theorems/0b52ef65-8a48-445f-a9bd-9a2c271ad6bb
-- title:
--   The corner parameter enumerates the symmetric order-three magic squares
-- statement:
--   **A bijection onto an interval.**
--
--   Let $S_{n}(t)$ denote the number of symmetric magic squares of order $n$ and
--   line sum $t$, and let $\mathrm{symmParamSet}(e)=\{0,1,\dots,2e\}$ be the
--   admissible corner parameters of the symmetric family, with
--   $\mathrm{symmParamCount}(e)=2e+1$. The theorem states
--
--   $$S_{3}(3e)=\mathrm{symmParamCount}(e).$$
--
--   That is, sending a symmetric magic square of order three and line sum $3e$ to
--   its top-left corner $M_{00}$ is a bijection onto $\{0,\dots,2e\}$.
--
--   **Proof.** The classification
--   `MagicSquares.symmetric_magic_three_classify` shows that such a square is
--   $\mathrm{symmMagic3}(e,a)$ with $a=M_{00}$, whose $(0,1)$ entry is $2e-a$; the
--   row-$0$ identity $a+(2e-a)+e=3e$ is then satisfiable in $\mathbb{N}$ only for
--   $a\le 2e$, so the map lands in $\mathrm{symmParamSet}(e)$. It is injective
--   because $a$ determines the whole square, and surjective because for every
--   $a\le 2e$ the array $\mathrm{symmMagic3}(e,a)$ is symmetric, is magic of line sum
--   $3e$, and has all entries at most $2e$, hence may be read over the ambient type
--   $\mathrm{Fin}(3e+1)$ of the counting function.
--
--   **Context.** This is the order-three counterpart of the bijection
--   `magic_three_param_bij` used in Mission I: there, MacMahon's two parameters
--   $(a,c)$ enumerate the magic squares of line sum $3e$; here the extra symmetry
--   condition cuts the parameter set down from the $\ell_{1}$ ball
--   $\{(a,c):|a-e|+|c-e|\le e\}$ to its diagonal slice $c=e$, an interval of $2e+1$
--   points. Composing the bijection with the cardinality of an interval gives the
--   closed form $S_{3}(3e)=2e+1$, and it also isolates *why* the count is linear
--   rather than quadratic in $e$.
-- source:
--   P. A. MacMahon, Combinatory Analysis, Vol. II, Cambridge University Press, 1916; M. Beck, T. Cohen, J. Cuomo and P. Gribelyuk, The number of "magic" squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707--717 (arXiv:math/0201013); W. S. Andrews, Magic Squares and Cubes, 2nd ed., Dover, 1960.

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresSpecial3
open MagicSquares

namespace MagicSquares

theorem symm_three_bij (e : ℕ) : symmetricMagicCount 3 (3 * e) = symmParamCount e := by sorry

end MagicSquares
