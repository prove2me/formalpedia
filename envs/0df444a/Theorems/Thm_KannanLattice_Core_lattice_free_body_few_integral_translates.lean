-- Prove2me | Theorems.Thm_KannanLattice_Core_lattice_free_body_few_integral_translates
-- name    : KannanLattice.Core.lattice_free_body_few_integral_translates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:14:53.350983+00:00
-- url     : https://prove2.me/theorems/b2043acc-4851-46f7-86ba-393f5caf048c
-- title:
--   Theorem (5.5) — a lattice-free convex body meets at most n^{2(n−dim V)} integer translates of an integral subspace V
-- statement:
--   Kannan states (Theorem (5.5)): *Suppose $K$ is any bounded convex body in $\mathcal R^n$ with $K\cap Z^n=\emptyset$. Then there is a $i$, $1\le i\le n$ and an $i$ dimensional space $V$ which has a basis of integer vectors such that the number of translates of $V$ containing lattice points that intersect $K$ is at most $n^{2(n-i+1)}$.*
--
--   Formalized statement. Let $n\ge2$ and let $K\subseteq\mathcal R^n$ be a bounded convex set with nonempty interior that contains no point of $\mathbb Z^n$. Then there is a linear subspace $V\subseteq\mathcal R^n$ spanned by integer vectors, with $1\le\dim V\le n-1$, such that
--
--   $$\#\{\,z+V : z\in\mathbb Z^n,\ (z+V)\cap K\neq\emptyset\,\}\ \le\ n^{2(n-\dim V)}.$$
--
--   For $\dim V=n-1$ this says that a lattice-free convex body lies between fewer than $n^2$ consecutive lattice hyperplanes of some integral direction, a flatness statement; smaller $\dim V$ trades a larger bound for a finer decomposition of $\mathbb Z^n$. It is the structural result behind Kannan's integer programming algorithm: the integer points of $K$ are searched translate by translate, each translate giving a lower-dimensional problem.
--
--   **Formalization Note** (1) *Dimension.* Read literally, the printed statement is trivial: $i=n$, $V=\mathcal R^n$ gives a single translate. The proof on the same page takes "$V$ the space spanned by $b_1,b_2,\dots b_{i-1}$", of dimension $i-1$, and adds "This ensures that the subspace $V$ is always of dimension at least 1"; it also calls $V=\{0\}$ "not interesting". The statement here is that reading: $\dim V=i-1\in[1,n-1]$ and bound $n^{2(n-i+1)}=n^{2(n-\dim V)}$. This forces $n\ge2$. (2) *Body.* "The word 'body' is used to denote a set of positive volume" (p. 28); for a convex set this is nonempty interior. $K$ is not assumed closed. (3) *Translates.* Only integer translates $z+V$, $z\in\mathbb Z^n$, are counted, as distinct sets, with the cardinality taken in $\mathbb N\cup\{\infty\}$, so the bound also asserts finiteness. $V$ is the real span of a set of integer points.
-- source:
--   Kannan, Minkowski's Convex Body Theorem and Integer Programming, Math. Oper. Res. 12 (1987); author's final manuscript (CMU-CS-96-105), p. 28, Theorem (5.5) (corrected reading: dim V = i − 1 ∈ [1, n − 1], as in the proof on the same page)

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice

namespace KannanLattice.Core

open Pointwise

/-- Theorem (5.5) of Kannan (1987), p. 28, in its corrected reading (the dimension of `V` is the
proof's `i − 1`, between `1` and `n − 1`): a bounded convex body `K ⊆ ℝⁿ` (`n ≥ 2`) containing no
integer point meets at most `n^{2(n − dim V)}` of the translates `z + V`, `z ∈ ℤⁿ`, of some linear
subspace `V` spanned by integer vectors with `1 ≤ dim V ≤ n − 1`. -/
theorem lattice_free_body_few_integral_translates (n : ℕ) (hn : 2 ≤ n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hconv : Convex ℝ K)
    (hbdd : Bornology.IsBounded K) (hbody : (interior K).Nonempty)
    (hfree : ∀ z : Fin n → ℤ, intPt z ∉ K) :
    ∃ V : Submodule ℝ (EuclideanSpace ℝ (Fin n)),
      (∃ S : Set (Fin n → ℤ), V = Submodule.span ℝ (intPt '' S)) ∧
      1 ≤ Module.finrank ℝ V ∧ Module.finrank ℝ V ≤ n - 1 ∧
      {A : Set (EuclideanSpace ℝ (Fin n)) |
          ∃ z : Fin n → ℤ, A = intPt z +ᵥ (V : Set (EuclideanSpace ℝ (Fin n))) ∧
            (A ∩ K).Nonempty}.encard ≤
        ((n ^ (2 * (n - Module.finrank ℝ V)) : ℕ) : ℕ∞) := by sorry

end KannanLattice.Core
