-- Prove2me | Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_127_product_no_five
-- name    : OddPerfectNumber.q2_five_q3_nineteen_q4_127_product_no_five
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T01:08:24.656381+00:00
-- url     : https://prove2.me/theorems/81300d22-117a-42c7-b365-87401e499dbc
-- title:
--   The q4=127 local sigma product cannot supply five
-- statement:
--   If the 3-, 19-, and 127-components cannot supply a factor 5, then the complete four-component local divisor-sum product cannot supply 5 either, since the 5-component cannot divide its own sigma.
-- source:
--   Prime-divisor elimination for a product of the four local sigma factors; the 5-component is handled by the accepted no-self-divisibility lemma.

import Mathlib
import Theorems.Thm_OddPerfectNumber_prime_not_dvd_own_sigma_prime_pow

namespace OddPerfectNumber

theorem q2_five_q3_nineteen_q4_127_product_no_five (a b c e : Nat)
    (h3 : ¬ 5 ∣ ∑ i ∈ Finset.range (a + 1), 3 ^ i)
    (h19 : ¬ 5 ∣ ∑ i ∈ Finset.range (c + 1), 19 ^ i)
    (h127 : ¬ 5 ∣ ∑ i ∈ Finset.range (e + 1), 127 ^ i) :
    ¬ 5 ∣
      (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (e + 1), 127 ^ i) := by
  sorry

end OddPerfectNumber
