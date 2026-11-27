-- Prove2me | Theorems.Thm_LefebvreVariations_cut_rank_weak_flags_dim_two
-- name    : LefebvreVariations.cut_rank_weak_flags_dim_two
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:18:41.204633+00:00
-- url     : https://prove2.me/theorems/5a77ecd8-9ebb-5fbd-9aa8-183467032b3c
-- title:
--   Lefebvre's variations, No. 250 — on a theme by Zhao, Chen, Li, Kong, Peng, Yu and Yue: the number of weak flags of subspaces of the plane over F2
-- statement:
--   Let $V$ be a $2$-dimensional vector space over $\mathbb F_2$ and $L\ge0$. The number $N_L$ of weak flags $U_1\supseteq U_2\supseteq\cdots\supseteq U_L$ of subspaces of $V$ satisfies
--   $$
--   N_L\ \le\ \prod_{j=1}^{2}(2^j-1)\binom{L+2}{2}\ =\ 3\binom{L+2}{2}\ \le\ 2^{3}(L+1)^2 .
--   $$
--
--   This is the case $q=2$ of the flag-counting bound $N_L\le\prod_{j=1}^q(2^j-1)\binom{L+q}{q}\le 2^{q(q+1)/2}(L+1)^q$ used in a dynamic-programming scheduling algorithm, which the platform lists as open for every dimension $q$. For $q=1$ the count is exactly $L+1$; $q=2$ is the first size with a genuine inequality.
--
--   **Formalization Note** A weak flag is an `Antitone` map `Fin L → Submodule (ZMod 2) V`; the dimension is given by `Module.finrank (ZMod 2) V = 2`. Both inequalities are stated, with the product and exponent written as in the general statement (`∏ j ∈ Finset.Icc 1 2, (2 ^ j - 1)` and `2 ^ (2 * (2 + 1) / 2)`). $L=0$ is allowed (one empty flag).
--
--   **Why this is a variation.** A variation on the open platform problem CutRankSched.lemma_5_3 (the number of weak flags in a q-dimensional F_2-space is at most prod (2^j - 1) binom(L+q, q) <= 2^{q(q+1)/2} (L+1)^q), played at q = 2 with the parent's statement restated verbatim, not imported. q = 1 is an equality (L+1); q = 2 is the first size with a real inequality. The statement for all q stays open.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Elementary counting. Source of the general statement: Zhao, Chen, Li, Kong, Peng, Yu, Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, Lemma 5.3 eq. (12), as quoted on the platform. In F_2^2 there are 1+3+1 subspaces; the number of weak flags is L+1+3L(L+1)/2 (checked by python enumeration for L=0..8: 1,5,12,22,35,51,70,92,117), against 3*binom(L+2,2) = 3,9,18,30,45,63,84,108,135.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- The case `q = 2` of `CutRankSched.lemma_5_3` (Eq. (12), counting descending weak flags): in a `2`-dimensional
vector space `V` over `𝔽₂`, the number of weak flags `U_1 ⊇ ⋯ ⊇ U_L` (antitone maps `Fin L → Submodule`) is at most
`(2¹ − 1)(2² − 1) · binom(L + 2, 2)`, and this is at most `2³ (L + 1)²`.
Source: elementary counting (a flag is a non-increasing sequence of subspaces of `𝔽₂²`, which has one subspace of
dimension 0, three of dimension 1, one of dimension 2); the exact counts for `L = 0, …, 8` are
`1, 5, 12, 22, 35, 51, 70, 92, 117`, below `3 · binom(L + 2, 2) = 3, 9, 18, 30, 45, 63, 84, 108, 135`
(checked by a python enumeration). -/
theorem cut_rank_weak_flags_dim_two (V : Type*) [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (L : ℕ) (hq : Module.finrank (ZMod 2) V = 2) :
    Nat.card {U : Fin L → Submodule (ZMod 2) V // Antitone U} ≤
        (∏ j ∈ Finset.Icc 1 2, (2 ^ j - 1)) * (L + 2).choose 2 ∧
      (∏ j ∈ Finset.Icc 1 2, (2 ^ j - 1)) * (L + 2).choose 2 ≤ 2 ^ (2 * (2 + 1) / 2) * (L + 1) ^ 2 := by
  sorry

end LefebvreVariations
