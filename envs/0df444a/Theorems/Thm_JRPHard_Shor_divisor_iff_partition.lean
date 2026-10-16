-- Prove2me | Theorems.Thm_JRPHard_Shor_divisor_iff_partition
-- name    : JRPHard.Shor.divisor_iff_partition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T12:39:42.49098+00:00
-- url     : https://prove2.me/theorems/31417059-af51-4bdb-97b5-e9a0f7b94a6b
-- title:
--   Appendix, p. 17 — unrounded divisor equivalence
-- statement:
--   Under the bit-range, even-total, and final multiplicative-window conditions, suppose also that every $p_i$ is prime. Put $M=\prod_i p_i$. Then
--   $$\bigl(\exists d\in\mathbb N:\ d\mid M,\ L\le d\le U\bigr)\quad\Longleftrightarrow\quad\text{the }a_i\text{ admit an equal-sum partition}.$$
--   The endpoints here are the real numbers $L$ and $U$. Primality connects divisors of the full product to subproducts, including when the list repeats a prime.
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, p. 17, Appendix, “In other words”

import Mathlib
import Definitions.Def_JRPHard_Shor_Setting

namespace JRPHard.Shor

open Finset

/-- Appendix, p. 17: the unrounded product of primes has a divisor in [L,U]
    exactly when the input is a yes instance of Partition. -/
theorem divisor_iff_partition (n B : ℕ) (hn : 0 < n) (hB : 1 ≤ B)
    (a : Fin n → ℕ) (ha : ∀ i, 2 ^ B ≤ a i ∧ a i < 2 ^ (B + 1))
    (heven : Even (∑ i, a i)) (p : Fin n → ℕ)
    (hp : ∀ i, (p i).Prime)
    (hwindow : ∀ i, (2 : ℝ) ^ (expo B a i) *
          (2 : ℝ) ^ (-(scale B / (2 * (n : ℝ)))) < (p i : ℝ) ∧
        (p i : ℝ) < (2 : ℝ) ^ (expo B a i) *
          (2 : ℝ) ^ (scale B / (2 * (n : ℝ)))) :
    (∃ d : ℕ, d ∣ ∏ i, p i ∧ lowL B a ≤ (d : ℝ) ∧
      (d : ℝ) ≤ highU B a) ↔ PartitionYes a := by sorry

end JRPHard.Shor
