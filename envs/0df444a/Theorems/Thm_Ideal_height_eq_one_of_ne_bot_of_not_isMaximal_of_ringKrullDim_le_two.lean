-- Prove2me | Theorems.Thm_Ideal_height_eq_one_of_ne_bot_of_not_isMaximal_of_ringKrullDim_le_two
-- name    : Ideal.height_eq_one_of_ne_bot_of_not_isMaximal_of_ringKrullDim_le_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/8ef9c755-8c19-5e62-8da7-b96232ac59e2
-- title:
--   Non-maximal non-zero primes have height one in dimension ≤ 2
-- statement:
--   Let $R$ be a commutative ring which is an integral domain and Noetherian, and suppose its Krull dimension satisfies $\operatorname{ringKrullDim} R \le 2$ (the inequality being taken in $\mathbb{Z} \cup \{\pm\infty\}$, i.e. in `WithBot ℕ∞`). Let $P$ be an ideal of $R$ that is prime, that is non-zero ($P \neq \bot$), and that is not a maximal ideal. Then the height of $P$, as an element of $\mathbb{N} \cup \{\infty\}$ — the supremum of the lengths of chains of primes descending from $P$ — equals $1$.
--
--   This is the elementary classification of primes in a Noetherian domain of Krull dimension at most two: apart from $(0)$ and the maximal ideals, every prime has height one. It is used in the analysis of two-dimensional chart rings arising in the study of curves over a discrete valuation ring, for instance in the results on valuation subrings and on the local models with crossing special fibre that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_height_eq_one_of_ne_bot_of_not_isMaximal_of_ringKrullDim_le_two.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Ideal.height_eq_one_of_ne_bot_of_not_isMaximal_of_ringKrullDim_le_two
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (hdim : ringKrullDim R ≤ 2) (P : Ideal R) [P.IsPrime] (hP0 : P ≠ ⊥) (hPm : ¬ P.IsMaximal) :
    P.height = 1 := by sorry
