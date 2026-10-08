-- Prove2me | Theorems.Thm_OddPerfectNumber_no_dris_five_s_ge_two_not_even_nonsq_odd_val_prime
-- name    : OddPerfectNumber.no_dris_five_s_ge_two_not_even_nonsq_odd_val_prime
-- status  : Open
-- author  : @vebis
-- created : 2026-10-05T18:19:50.836346+00:00
-- url     : https://prove2.me/theorems/7f2be7d3-65d8-4bde-bc7d-dc1c33bdea5c
-- title:
--   Dris five-case, odd non-square $s$: with a prime $\ell\ne3$ of $p^4+p^2+1$ dividing $s$ to an odd power
-- statement:
--   This is the non-square-index subcase of the Dris $k=5$, $s\ge 2$ odd leaf (`no_dris_five_s_ge_two_not_even_nonsq`), with one additional hypothesis: the index $s$ is divisible to an **odd power** by some prime $\ell\ne 3$ dividing $p^4+p^2+1$. For $p$ an odd prime, $m$ odd with $p\nmid m$, and $s\ge 2$ odd and not a perfect square, the pair of relations
--   $$2m^{2}=\sigma(p^{5})\,s,\qquad \sigma(m^{2})=p^{5}s$$
--   is impossible.
--
--   The extra hypothesis is not a genuine restriction of the original leaf: by `OddPerfectNumber.five_dris_index_odd_valuation_prime` it follows from the first relation alone. It records, for anyone attacking the leaf, that $s$ always carries an odd power of a prime $\ell\equiv 1\pmod 6$ dividing $p^4+p^2+1$, in particular $s\ge 7$ and $s$ is not a power of $3$.
--
--   **Formalization Note** The conclusion is stated exactly as in the parent leaf, as $\neg(\text{both relations})$.
-- source:
--   https://prove2.me/missions/f37bda44-314b-4d8e-8917-fe26209e0c9c

import Mathlib

namespace OddPerfectNumber

theorem no_dris_five_s_ge_two_not_even_nonsq_odd_val_prime (p m s : Nat) (hp : p.Prime)
    (hp2 : p != 2) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m) (hs2 : 2 ≤ s)
    (hs_not_even : ¬ Even s) (hs_nsq : ¬ ∃ r, s = r ^ 2)
    (hl : ∃ ℓ : Nat, ℓ.Prime ∧ ℓ ≠ 3 ∧ ℓ ∣ p ^ 4 + p ^ 2 + 1 ∧ Odd (padicValNat ℓ s)) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ 5).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * s) := by sorry

end OddPerfectNumber
