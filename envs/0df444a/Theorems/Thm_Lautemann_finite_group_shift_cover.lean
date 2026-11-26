-- Prove2me | Theorems.Thm_Lautemann_finite_group_shift_cover
-- name    : Lautemann.finite_group_shift_cover
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:21:39.473355+00:00
-- url     : https://prove2.me/theorems/85a30808-011f-4c9d-a2c7-a3950bd57508
-- title:
--   Lautemann’s shift-cover counting lemma for finite groups
-- statement:
--   Let $G$ be a finite group of order $N$. A Boolean test on $G$ rejects exactly $b$ elements. For any nonnegative integer $t$ satisfying
--   $$N b^t < N^t,$$
--   there are shifts $s_1,\ldots,s_t\in G$ such that every $x\in G$ passes at least one of the tests at $x s_1,\ldots,x s_t$. The same shifts work for all $x$. Multiplication is on the right and $G$ may be noncommutative.
--
--   For $r$-bit strings under XOR, if at most half of the strings fail, the inequality holds for $t=r+1$.
-- source:
--   Finite-group generalization of the translate-counting argument in C. Lautemann, BPP and the polynomial hierarchy, Information Processing Letters 17 (1983), 215–217, https://doi.org/10.1016/0020-0190(83)90044-3. For the Boolean-cube covering statement see E. Blais, Models of Computation, §15, BPP and the Polynomial Hierarchy, Lemma 2, https://cs.uwaterloo.ca/~eblais/cs365/w26/P-and-BPP. Related platform theorem (Boolean cube): https://prove2.me/theorems/24f83c32-a520-484e-8d00-bb144437bea0.

import Mathlib

theorem Lautemann.finite_group_shift_cover {G : Type*} [Group G] [Fintype G]
    (pass : G → Bool) (t : ℕ)
    (few : Fintype.card G * Fintype.card {x : G // pass x = false} ^ t <
      Fintype.card G ^ t) :
    ∃ shifts : Fin t → G, ∀ seed : G, ∃ j, pass (seed * shifts j) = true := by sorry
