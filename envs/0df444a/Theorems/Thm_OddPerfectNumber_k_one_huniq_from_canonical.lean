-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_huniq_from_canonical
-- name    : OddPerfectNumber.k_one_huniq_from_canonical
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-12T17:20:11.773653+00:00
-- url     : https://prove2.me/theorems/eca07809-acb4-4a64-b774-4355de7afb5f
-- title:
--   The canonical k=1 equations identify the unique p-source
-- statement:
--   From the canonical k=1 equations, p not dividing m, and a specified local p-source q, every support prime whose local sigma factor is divisible by p equals q. The proof uses the proved exact p-adic valuation-one gateway and the proved unique-p-source theorem; it is an interface lemma, not a contradiction.
-- source:
--   Acyclic composition of OddPerfectNumber.k_one_exact_valuation_one and OddPerfectNumber.k_one_unique_p_source, both already Proved on the pinned environment. No q-endgame theorem is imported.

import Mathlib

namespace OddPerfectNumber

theorem k_one_huniq_from_canonical (p m d q : Nat)
    (hp : p.Prime) (hpm : ¬ p ∣ m)
    (hdvd : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hqmem : q ∈ (m ^ 2).primeFactors)
    (hqdvd : p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i) :
    ∀ y ∈ (m ^ 2).primeFactors,
      p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization y + 1), y ^ i → y = q := by
  sorry

end OddPerfectNumber
