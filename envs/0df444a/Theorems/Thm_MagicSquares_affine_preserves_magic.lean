-- Prove2me | Theorems.Thm_MagicSquares_affine_preserves_magic
-- name    : MagicSquares.affine_preserves_magic
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-16T15:06:09.095007+00:00
-- url     : https://prove2.me/theorems/2e82f714-7b8e-4902-81bf-35bb9bf56c81
-- title:
--   Affine substitution preserves the magic property
-- statement:
--   **Affine substitution.** Let $A$ be a magic square of order $n$ with line sum
--   $S$, and let $a,b$ be scalars. The array $A'$ with entries
--
--   $$
--   A'_{ij} \;=\; a\,A_{ij} + b
--   $$
--
--   is again magic, with line sum
--
--   $$
--   S' \;=\; aS + nb .
--   $$
--
--   Each line has exactly $n$ entries, so its sum becomes $aS+nb$; this applies to
--   rows, columns and both main diagonals alike. The shift by $b$ contributes $nb$
--   because it is added $n$ times along the line.
--
--   Two consequences drive the enumerative theory. Taking $a=1$ shows that the
--   counting function depends only on the line sum up to translation, and taking
--   $a=-1,\ b=n^{2}+1$ over $\mathbb{Z}$ gives the classical *complement*
--   $A\mapsto n^{2}+1-A$, which sends a normal magic square of order $n$ to another
--   one with line sum $n(n^{2}+1)-S$.
--
--   **Formalization Note** `affine a b M` is the entrywise map from
--   `Definitions.Def_MagicSquaresTransforms`. The ring law is used only to distribute
--   $a$ over a finite sum and to collapse $\sum_{j} b$ to $n\bullet b$.
-- source:
--   Beck, Cohen, Cuomo & Gribelyuk, The number of ``magic'' squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707--717; arXiv:math/0201013v3.

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresTransforms

namespace MagicSquares

theorem affine_preserves_magic {n : ℕ} {α : Type*} [Semiring α]
    (M : Square n α) (s a b : α) (hM : IsMagic M s) :
    IsMagic (affine a b M) (a * s + n • b) := by sorry

end MagicSquares
