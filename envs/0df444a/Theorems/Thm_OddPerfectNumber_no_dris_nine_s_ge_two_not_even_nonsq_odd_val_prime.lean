-- Prove2me | Theorems.Thm_OddPerfectNumber_no_dris_nine_s_ge_two_not_even_nonsq_odd_val_prime
-- name    : OddPerfectNumber.no_dris_nine_s_ge_two_not_even_nonsq_odd_val_prime
-- status  : Open
-- author  : @Himan
-- created : 2026-11-15T04:00:07.72421+00:00
-- url     : https://prove2.me/theorems/cf261186-d1b5-48ea-8be7-0bbec22fc7a2
-- title:
--   Dris nine-case, odd non-square $s$: with a prime $\ell\equiv 1 \pmod{10}$ of $p^8+p^6+p^4+p^2+1$ dividing $s$ to an odd power
-- statement:
--   This is the non-square-index Dris leaf at special exponent $k=9$ (`OddPerfectNumber.no_dris_nine_s_ge_two_not_even_nonsq`) with one additional hypothesis on the index.
--
--   Let $p$ be a prime with $p\equiv 1\pmod 4$, let $k=9$, let $m$ be odd with $p\nmid m$, and let $s\ge 2$ be odd and not a perfect square. Assume moreover that some prime $\ell\equiv 1\pmod{10}$ dividing $p^{8}+p^{6}+p^{4}+p^{2}+1$ divides $s$ to an odd power. Then the pair of Dris relations
--   $$2m^{2}=\sigma(p^{9})\,s,\qquad \sigma(m^{2})=p^{9}s$$
--   cannot both hold, where $\sigma$ denotes the sum of all positive divisors.
--
--   The extra hypothesis is not a genuine restriction of the parent leaf: by `OddPerfectNumber.nine_dris_index_odd_valuation_prime` it follows from the first relation alone. It records, for anyone working on the leaf, that the index always carries an odd power of a prime $\ell\equiv 1\pmod{10}$ that divides $\Phi_5(p)\,\Phi_{10}(p)$; in particular $s\ge 11$ and $s$ is not a power of $3$, $5$ or $7$.
--
--   **Formalization Note** The binders and the conclusion are those of the parent leaf, including the redundant pair `k % 4 = 1`, `k = 9`, and the conclusion is stated as the negation of the conjunction of the two relations. The statement is an elementary refinement written for this mission; it is not taken from the literature.
-- source:
--   https://prove2.me/missions/f37bda44-314b-4d8e-8917-fe26209e0c9c

import Mathlib

namespace OddPerfectNumber

theorem no_dris_nine_s_ge_two_not_even_nonsq_odd_val_prime (p k m s : Nat) (hp : p.Prime)
    (hp2 : p != 2) (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hk9 : k = 9) (hm : Odd m)
    (hpm : ¬ p ∣ m) (hs2 : 2 ≤ s) (hs_not_even : ¬ Even s) (hs_nsq : ¬ ∃ r, s = r ^ 2)
    (hl : ∃ ℓ : Nat, ℓ.Prime ∧ ℓ % 10 = 1 ∧ ℓ ∣ p ^ 8 + p ^ 6 + p ^ 4 + p ^ 2 + 1 ∧
      Odd (padicValNat ℓ s)) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by sorry

end OddPerfectNumber
