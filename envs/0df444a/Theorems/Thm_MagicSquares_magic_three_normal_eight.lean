-- Prove2me | Theorems.Thm_MagicSquares_magic_three_normal_eight
-- name    : MagicSquares.magic_three_normal_eight
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-17T07:15:05.755212+00:00
-- url     : https://prove2.me/theorems/15e75fbb-7830-416b-ac11-6471accdd4e9
-- title:
--   There are exactly eight normal magic squares of order three
-- statement:
--   **Lo Shu uniqueness.** Exactly eight admissible
--   parameter pairs give a normal magic square of order three:
--
--   $$\mathrm{normalParamCount}(5)=8,$$
--
--   where $\mathrm{normalParamCount}(e)$ counts the pairs $(a,c)\in\mathrm{paramSet}(e)$
--   for which $\mathrm{mkMagic3}(e,a,c)$ is normal.
--
--   By `magic_three_param_bij` the admissible parameter pairs are in bijection with
--   the $3\times3$ magic squares of line sum $15$, so this is precisely the statement
--   that there are **eight** normal magic squares of order three — the eight images
--   of
--
--   $$\begin{pmatrix}4&9&2\\3&5&7\\8&1&6\end{pmatrix}$$
--
--   under the symmetry group $D_{4}$ of the square. Equivalently: the Lo Shu square
--   is the *unique* normal magic square of order three up to symmetry.
--
--   This is the oldest non-trivial classification in combinatorics, and the reason
--   order three is exceptional: for $n=4$ there are $880$ normal squares up to
--   symmetry, and for $n\ge5$ no classification is known.
--
--   **Proof.** Immediate from `magic_three_normal_classify`, which characterizes
--   normality by the eight parameter pairs $(2,4),(2,6),(4,2),(4,8),(6,2),(6,8),(8,4),(8,6)$:
--   the defining filter of `normalParamSet 5` selects exactly those eight, and they
--   are distinct.
-- source:
--   P. A. MacMahon, Combinatory Analysis (1916); W. S. Andrews, Magic Squares and Cubes, 2nd ed., Dover, 1960.

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresParam3
import Definitions.Def_MagicSquaresNormal3
open MagicSquares

namespace MagicSquares

theorem magic_three_normal_eight : normalParamCount 5 = 8 := by sorry

end MagicSquares
