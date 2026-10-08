-- Prove2me | Theorems.Thm_KingmanSubadditive_Ulam_expected_num_ascending
-- name    : KingmanSubadditive.Ulam.expected_num_ascending
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:46:00.865411+00:00
-- url     : https://prove2.me/theorems/d6bb962a-7955-4c5c-b473-51517a1f9eb7
-- title:
--   Proof of Theorem 8, p. 896 — E(ν) = (n choose k)(k!)⁻¹ for the number ν of ascending k-sequences
-- statement:
--   Let $k$ be a positive integer, let $\pi$ be drawn from the uniform distribution on $\mathcal S_n$, and let $\nu$ be the number of sequences $i_1<i_2<\dots<i_k\le n$ with $\pi(i_1)<\pi(i_2)<\dots<\pi(i_k)$. Then
--   $$E(\nu)=\sum_{i_1<i_2<\dots<i_k}P\{\pi(i_1)<\pi(i_2)<\dots<\pi(i_k)\}=\binom nk\,(k!)^{-1}.$$
--
--   This first-moment computation is the input of the tail bound (2.4.7) on $l(\pi)$.
--
--   **Formalization Note** The expectation under the uniform law is the average of $\nu$ over the $n!$ permutations.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 896, §2.4, proof of Theorem 8

import Mathlib
import Definitions.Def_KingmanSubadditive_Ulam_Permutations

open scoped BigOperators

namespace KingmanSubadditive.Ulam

/-- The first moment of `ν` (Kingman, *Subadditive ergodic theory*, Ann. Probab.
1(6):883–899 (1973), §2.4, proof of Theorem 8, p. 896). Let `k` be a positive integer, let `π` be
uniform on `𝒮_n` and let `ν` be the number of sequences `i₁ < ⋯ < i_k ≤ n` with
`π(i₁) < ⋯ < π(i_k)`. Then `E(ν) = (n choose k)(k!)⁻¹`.

**Formalization Note** The expectation under the uniform law is the average over the `n!`
permutations of `Fin n`. -/
theorem expected_num_ascending (n k : ℕ) (hk : 0 < k) :
    (∑ σ : Equiv.Perm (Fin n), (numAscending k σ : ℝ)) / (Nat.factorial n : ℝ) =
      (n.choose k : ℝ) / (Nat.factorial k : ℝ) := by sorry

end KingmanSubadditive.Ulam
