-- Prove2me | Theorems.Thm_MagicSquares_sm3_canonical
-- name    : MagicSquares.sm3_canonical
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-16T18:23:46.645456+00:00
-- url     : https://prove2.me/theorems/650b0511-bff1-4101-84b1-a49d5bef9849
-- title:
--   Canonical decomposition of a 3x3 semi-magic square
-- statement:
--   Every $3\times3$ semi-magic square with
--   nonnegative integer entries and line sum $t$ can be written **uniquely** as a
--   nonnegative integer combination
--
--   $$M=u\,D+v\,E+w\,F+x\,A+y\,B+z\,C$$
--
--   of the six order-three permutation matrices, normalized by
--   $\min(x,y,z)=0$. Here $D,E,F$ are the three even transversals (the identity and
--   the two $3$-cycles) and $A,B,C$ the three odd ones (the transpositions).
--
--   **Existence.** Put $u=\min D$, $v=\min E$, $w=\min F$ and subtract
--   $uD+vE+wF$; the residual $M'$ is again semi-magic and each of its three even
--   transversals has minimum $0$. Writing $M'$ in the four-parameter form
--   $$\begin{pmatrix} a & b & t'-a-b\\ c & d & t'-c-d\\
--   t'-a-c & t'-b-d & a+b+c+d-t'\end{pmatrix},$$
--   the three vanishing minima read
--   $$\min(a,d,a+b+c+d-t')=\min(b,t'-c-d,t'-a-c)=\min(t'-a-b,c,t'-b-d)=0.$$
--   If $b>c$ then each of the three ways for the middle minimum to vanish forces
--   the opposite inequality: $b=0$ is impossible, $t'-c-d=0$ gives $c+d=t'$ and
--   hence $b\le c$ from $b+d\le t'$, and $t'-a-c=0$ gives $a+c=t'$ and hence
--   $b\le c$ from $a+b\le t'$. So $b\le c$, and symmetrically $c\le b$; thus
--   $b=c$, which is exactly the statement that $M'$ is a combination of $A,B,C$
--   alone.
--
--   **Uniqueness.** The normalization is essential: without it the single relation
--   $D+E+F=A+B+C$ (both sides equal the all-ones matrix) would identify distinct
--   $6$-tuples. With $\min(x,y,z)=0$ the coefficients are recovered from $M$ by
--   $u=\min D$, $v=\min E$, $w=\min F$ and $x=M_{00}-u$, $y=M_{11}-u$, $z=M_{01}-v$.
--
--   **Formalization Note** `sm3Of` is defined over $\mathbb{N}$ with truncated
--   subtraction where necessary, so every recovery identity has to be stated with
--   the admissibility inequalities as explicit hypotheses.
-- source:
--   P. A. MacMahon, Combinatory Analysis (1915); M. Beck, T. Cohen, J. Cuomo, P. Gribelyuk, The number of "magic" squares, cubes and hypercubes, Amer. Math. Monthly 110 (2003), 707-717; arXiv:math/0201013v3, Section 2, Theorem 1.

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresSemiMagic3
open MagicSquares

namespace MagicSquares

theorem sm3_canonical (M : Square 3 ℕ) (t : ℕ) (hM : IsSemiMagic M t) :
    ∃ u v w x y z : ℕ,
      M = sm3Of u v w x y z ∧
        u + v + w + x + y + z = t ∧
          min x (min y z) = 0 ∧
            ∀ u' v' w' x' y' z' : ℕ,
              M = sm3Of u' v' w' x' y' z' →
                min x' (min y' z') = 0 →
                  u' = u ∧ v' = v ∧ w' = w ∧ x' = x ∧ y' = y ∧ z' = z := by sorry

end MagicSquares
