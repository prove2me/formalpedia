-- Prove2me | Theorems.Thm_ModernConvex_LPDuality_radon_theorem
-- name    : ModernConvex.LPDuality.radon_theorem
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:31:51.59506+00:00
-- url     : https://prove2.me/theorems/bab54875-54ae-4c8e-9a8c-9ba3e5cc81cc
-- title:
--   Theorem 1.4.3 — Radon: $m \ge n+2$ points of $\mathbb R^n$ split into two parts with intersecting convex hulls
-- statement:
--   Let $a_1,\dots,a_m$ be a collection of $m$ vectors in $\mathbb R^n$ with
--   $$m \ge n + 2.$$
--   Then there is a partition of the index set $\{1,\dots,m\}$ into two nonempty disjoint subsets $I$ and $J$ such that
--   $$\operatorname{conv}\{a_i : i \in I\} \;\cap\; \operatorname{conv}\{a_i : i \in J\} \neq \emptyset.$$
--
--   Radon's theorem is the step from which the book derives Helly's theorem (Exercise 1.14), and through it the homogeneous Farkas lemma and the theorem on the alternative.
--
--   **Formalization Note** The collection is a function $a : \{0,\dots,m-1\} \to \mathbb R^n$ (repetitions allowed, as for a list of vectors). "Partition into two nonempty disjoint subsets" is: $I$ and $J$ nonempty, disjoint, with union the whole index set.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 38, Theorem 1.4.3 (Radon)

import Mathlib

namespace ModernConvex.LPDuality

/-- Ben-Tal–Nemirovski, Theorem 1.4.3 (Radon), p. 38. -/
theorem radon_theorem {n m : ℕ} (a : Fin m → Fin n → ℝ) (hm : n + 2 ≤ m) :
    ∃ I J : Finset (Fin m), I.Nonempty ∧ J.Nonempty ∧ Disjoint I J ∧ I ∪ J = Finset.univ ∧
      (convexHull ℝ (a '' (I : Set (Fin m))) ∩ convexHull ℝ (a '' (J : Set (Fin m)))).Nonempty := by sorry

end ModernConvex.LPDuality
