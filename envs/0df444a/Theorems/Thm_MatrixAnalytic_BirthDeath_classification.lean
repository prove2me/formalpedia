-- Prove2me | Theorems.Thm_MatrixAnalytic_BirthDeath_classification
-- name    : MatrixAnalytic.BirthDeath.classification
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:42:41.518006+00:00
-- url     : https://prove2.me/theorems/f35ed635-df63-4e66-aae9-165ba56f3177
-- title:
--   Theorem 4.2.3 — recurrence and positive recurrence of a birth-and-death chain, and its stationary distribution
-- statement:
--   Let $P$ be the transition matrix (4.5) of an irreducible birth-and-death chain on $\{0,1,2,\dots\}$, with $a_{ij}=P(i,j)$, and let $R_n$ be the expected number of visits to $n$ between two successive visits to $n-1$. Then:
--
--   1. the chain is recurrent if and only if $R_n = a_{n-1,n}/a_{n,n-1}$ for all $n\ge1$;
--   2. it is positive recurrent if and only if
--   $$\sum_{k\ge1}\frac{a_{01}\cdots a_{k-1,k}}{a_{10}\cdots a_{k,k-1}}<\infty;$$
--   3. in that case it has a stationary distribution $\pi$, and every stationary distribution satisfies
--   $$\pi_0=\Big(1+\sum_{k\ge1}\frac{a_{01}\cdots a_{k-1,k}}{a_{10}\cdots a_{k,k-1}}\Big)^{-1},\qquad \pi_n=\pi_0\frac{a_{01}\cdots a_{n-1,n}}{a_{10}\cdots a_{n,n-1}}\quad\text{for all }n\ge1.$$
--
--   This is the complete classification of irreducible birth-and-death chains together with the product form of their stationary distribution.
--
--   **Formalization Note** Recurrence and positive recurrence are stated at state $0$ (by irreducibility, equivalent to every state). The book's $\pi$ in the positive recurrent case is the stationary distribution, which it describes as the unique solution of $\pi P=\pi$, $\pi\mathbf 1=1$ (p. 88); the Lean statement asserts that one exists and that every stationary distribution (nonnegative, summing to one, $\pi P=\pi$) is given by the formulas. Products are written $\prod_{i=0}^{k}a_{i,i+1}/a_{i+1,i}$, which equals the book's ratio of products since all denominators are positive.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 90, Theorem 4.2.3

import Mathlib
import Definitions.Def_MatrixAnalytic_BirthDeath_Chain
import Definitions.Def_MatrixAnalytic_BirthDeath_Model
import Definitions.Def_MatrixAnalytic_BirthDeath_Passage

namespace MatrixAnalytic.BirthDeath

theorem classification (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) :
    (Recurrent P 0 ↔ ∀ n : ℕ, R P (n + 1) = P n (n + 1) / P (n + 1) n) ∧
    (PositiveRecurrent P 0 ↔
      Summable (fun k : ℕ => ∏ i ∈ Finset.range (k + 1), P i (i + 1) / P (i + 1) i)) ∧
    (PositiveRecurrent P 0 →
      (∃ π : ℕ → ℝ, IsStationaryC P π) ∧
      ∀ π : ℕ → ℝ, IsStationaryC P π →
        π 0 = (1 + ∑' k : ℕ, ∏ i ∈ Finset.range (k + 1), P i (i + 1) / P (i + 1) i)⁻¹ ∧
        ∀ n : ℕ, π (n + 1) =
          π 0 * ∏ i ∈ Finset.range (n + 1), P i (i + 1) / P (i + 1) i) := by sorry

end MatrixAnalytic.BirthDeath
