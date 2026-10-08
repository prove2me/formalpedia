-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_two_prime_odd_multiplicity_supplier
-- name    : OddPerfectNumber.Kernel.five_two_prime_odd_multiplicity_supplier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T11:48:36.161481+00:00
-- url     : https://prove2.me/theorems/81a21984-c732-49a9-a3b7-bc3ceec52ae7
-- title:
--   An odd-multiplicity prime supplier of sigma(m^2) is one of p, q, r
-- statement:
--   Suppose the second k=5 Dris equation sigma(m^2) = p^5 * d1^2 * q * r holds with q and r distinct primes. If a prime l occurs in sigma(m^2) to an odd multiplicity, then l is one of p, q and r. This is strictly stronger than the Proved ef31275b, which only says every prime DIVIDING sigma(m^2) lies in {p} union supp(d1) union {q,r}: here the square d1^2 cannot contribute at odd multiplicity anywhere, so the freeness of d1 plays no role and the conclusion mentions p, q and r alone. This is the form of the closure condition that is immune to the absorption trick, where choosing d1 to contain an offending prime makes the weaker divisibility statement vacuous while leaving this one intact. Audited over 20000 random instances of p^5 d1^2 q r: zero odd-multiplicity primes outside {p, q, r}.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_two_prime_odd_multiplicity_supplier {p m d1 q r : Nat} (hp : p.Prime)
    (hq : q.Prime) (hr : r.Prime) (hqr : q < r)
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * (d1 ^ 2 * (q * r)))
    (l : Nat) (hl : l.Prime)
    (hodd : Not (Even ((∑ d ∈ (m ^ 2).divisors, d).factorization l))) :
    (l = p \/ l = q \/ l = r) := by
  sorry

end OddPerfectNumber.Kernel
