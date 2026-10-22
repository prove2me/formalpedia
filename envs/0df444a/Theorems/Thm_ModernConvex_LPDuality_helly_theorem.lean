-- Prove2me | Theorems.Thm_ModernConvex_LPDuality_helly_theorem
-- name    : ModernConvex.LPDuality.helly_theorem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:31:52.479848+00:00
-- url     : https://prove2.me/theorems/686147b0-5cc6-4d71-86f9-062d1cd3ce61
-- title:
--   Theorem 1.4.2 — Helley theorem: if every $k \le n+1$ of finitely many convex sets in $\mathbb R^n$ meet, all of them meet
-- statement:
--   Let $A_1,\dots,A_M$ be a finite collection of convex sets in $\mathbb R^n$. Assume that the intersection of every $k \le n+1$ sets from the collection is nonempty: for every set $S \subseteq \{1,\dots,M\}$ of at most $n+1$ indices,
--   $$\bigcap_{i \in S} A_i \neq \emptyset .$$
--   Then the intersection of all $M$ sets is nonempty:
--   $$\bigcap_{i=1}^M A_i \neq \emptyset .$$
--
--   In the book (which spells the name "Helley") this theorem gives the "intelligent", purely algebraic proof of the homogeneous Farkas lemma (Exercise 1.13), and hence of the theorem on the alternative and of LP duality.
--
--   **Formalization Note** The sets are indexed by $\{0,\dots,M-1\}$; subcollections are finite sets of indices $S$ with $|S| \le n+1$. The empty subcollection has intersection $\mathbb R^n$, so the hypothesis says nothing for $k = 0$. No lower bound on $M$ is imposed: for $M \le n+1$ the hypothesis with $S$ the whole index set is already the conclusion, exactly as in the book's statement.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 37, Theorem 1.4.2 (Helley theorem)

import Mathlib

namespace ModernConvex.LPDuality

/-- Ben-Tal–Nemirovski, Theorem 1.4.2 (Helley theorem), p. 37. -/
theorem helly_theorem {n M : ℕ} (A : Fin M → Set (Fin n → ℝ)) (hconv : ∀ i, Convex ℝ (A i))
    (hinter : ∀ S : Finset (Fin M), S.card ≤ n + 1 → (⋂ i ∈ S, A i).Nonempty) :
    (⋂ i, A i).Nonempty := by sorry

end ModernConvex.LPDuality
