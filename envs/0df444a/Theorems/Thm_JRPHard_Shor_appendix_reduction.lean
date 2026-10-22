-- Prove2me | Theorems.Thm_JRPHard_Shor_appendix_reduction
-- name    : JRPHard.Shor.appendix_reduction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T12:39:27.689012+00:00
-- url     : https://prove2.me/theorems/caf5c20a-27a1-46f1-a574-81f7d9e29097
-- title:
--   Appendix reduction — Partition iff rounded RangeDivisor
-- statement:
--   Let $n\ge1$, $B\ge1$, and let $2^B\le a_i<2^{B+1}$ be an indexed Partition input with even total. Set $\lambda=3B/2^B$, $A=\frac12\sum_i a_i$, $b_i=\lambda a_i$, $L=2^{\lambda(A-1/2)}$, and $U=2^{\lambda(A+1/2)}$. Let $p_i$ be primes in the printed open windows
--   $$2^{b_i}-cb_i2^{b_i/2}<p_i<2^{b_i}+cb_i2^{b_i/2},$$
--   where the real constant $c$ obeys $cb_i<\lambda2^{b_i/2}/(4n)$ for each $i$. Suppose also that $2^{\lambda/2}+2^{-\lambda/2}<2\sqrt2$. With $M=\prod_i p_i$, the rounded triple $(M,\lceil L\rceil,\lfloor U\rfloor)$ is a valid RangeDivisor instance, and
--   $$M\text{ has a divisor in }[\lceil L\rceil,\lfloor U\rfloor]\quad\Longleftrightarrow\quad (a_i)\text{ has an equal-sum partition}.$$
--   This is the mathematical correctness of the Appendix reduction. It retains the sampled-prime windows and asserts the full rounded instance condition.
--
--   **Formalization Note** Evenness is added because the printed converse fails for odd totals; a computational reduction sends odd-total inputs to a fixed no instance. The theorem assumes the paper's displayed quantitative conditions in place of “sufficiently large $B$.” It does not assert the existence or efficient sampling of the primes or any complexity classification.
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, p. 17, Appendix conclusion, with p. 15 rounding

import Mathlib
import Definitions.Def_JRPHard_Shor_Setting

namespace JRPHard.Shor

open Finset

/-- Appendix, p. 17 together with rounding from p. 15: the explicit sampled
    prime product is a RangeDivisor yes instance iff Partition is yes. -/
theorem appendix_reduction (n B : ℕ) (hn : 0 < n) (hB : 1 ≤ B)
    (a : Fin n → ℕ) (ha : ∀ i, 2 ^ B ≤ a i ∧ a i < 2 ^ (B + 1))
    (heven : Even (∑ i, a i)) (c : ℝ)
    (hc : ∀ i, c * expo B a i <
      scale B * (2 : ℝ) ^ (expo B a i / 2) / (4 * (n : ℝ)))
    (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime)
    (hwin : ∀ i,
      (2 : ℝ) ^ (expo B a i) - c * expo B a i *
        (2 : ℝ) ^ (expo B a i / 2) < (p i : ℝ) ∧
      (p i : ℝ) < (2 : ℝ) ^ (expo B a i) + c * expo B a i *
        (2 : ℝ) ^ (expo B a i / 2))
    (hlam : (2 : ℝ) ^ (scale B / 2) +
      (2 : ℝ) ^ (-(scale B / 2)) < 2 * Real.sqrt 2) :
    JRPHard.RangeDiv.IsRangeDivisorInstance (∏ i, p i) ⌈lowL B a⌉₊ ⌊highU B a⌋₊ ∧
      (JRPHard.RangeDiv.HasDivisorIn (∏ i, p i) ⌈lowL B a⌉₊ ⌊highU B a⌋₊ ↔
        PartitionYes a) := by sorry

end JRPHard.Shor
