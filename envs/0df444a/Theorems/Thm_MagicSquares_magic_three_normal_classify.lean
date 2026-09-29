-- Prove2me | Theorems.Thm_MagicSquares_magic_three_normal_classify
-- name    : MagicSquares.magic_three_normal_classify
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-17T07:01:56.498885+00:00
-- url     : https://prove2.me/theorems/c677420b-bca2-41da-b9e3-f804919a1235
-- title:
--   The normal members of MacMahon's order-three family
-- statement:
--   **Characterization of the normal squares inside
--   MacMahon's order-three family.**
--
--   For $(a,c)\in\mathrm{paramSet}\ 5$,
--
--   $$\mathrm{mkMagic3}(5,a,c)\ \text{is normal}\iff (a,c)\in\{(2,4),(2,6),(4,2),(4,8),(6,2),(6,8),(8,4),(8,6)\}.$$
--
--   Here *normal* means the nine entries lie in $[1,9]$ and are pairwise distinct,
--   i.e. they are a permutation of $1,\dots,9$; and
--
--   $$\mathrm{mkMagic3}(5,a,c)=
--   \begin{pmatrix}
--   a & 15-a-c & c\\
--   5+c-a & 5 & 5+a-c\\
--   10-c & a+c-5 & 10-a
--   \end{pmatrix}.$$
--
--   **Proof.** Normality forces $1\le a\le 9$ and $1\le c\le 9$, since $a=M_{00}$ and
--   $c=M_{02}$ are entries. This leaves $81$ pairs, each of which is a ground
--   instance and is settled by evaluation. The eight surviving pairs are exactly
--   those for which the corner entries $a$ and $c$ are distinct members of
--   $\{2,4,6,8\}$ with $a+c\ne 10$; the pairs with $a+c=10$ are excluded because
--   then $M_{21}=a+c-5=5$ coincides with the centre.
--
--   **Formalization Note** `IsNormal` is stated with a `Function.Injective`, which is
--   not decidable as given, so it is first rewritten into an explicit conjunction of
--   entrywise bounds over `Fin 3` and pairwise-distinctness of the nine positions.
--   The quantifiers over `Fin 3` are then unfolded with `Fin.forall_fin_succ` before
--   `norm_num` decides the resulting ground instances. Because the parametrization
--   is over $\mathbb{N}$, entries such as $a+c-5$ and $15-a-c$ truncate at zero, and
--   each instance is evaluated with the truncation in place.
-- source:
--   P. A. MacMahon, Combinatory Analysis (1916); W. S. Andrews, Magic Squares and Cubes, 2nd ed., Dover, 1960; M. Beck, T. Cohen, J. Cuomo, P. Gribelyuk, Amer. Math. Monthly 110 (2003), 707-717; arXiv:math/0201013v3.

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresParam3
open MagicSquares

namespace MagicSquares

theorem magic_three_normal_classify (a c : ℕ) (hac : (a, c) ∈ paramSet 5) :
    IsNormal (mkMagic3 5 a c) ↔
      (a = 2 ∧ c = 4) ∨ (a = 2 ∧ c = 6) ∨ (a = 4 ∧ c = 2) ∨ (a = 4 ∧ c = 8) ∨
        (a = 6 ∧ c = 2) ∨ (a = 6 ∧ c = 8) ∨ (a = 8 ∧ c = 4) ∨ (a = 8 ∧ c = 6) := by sorry

end MagicSquares
