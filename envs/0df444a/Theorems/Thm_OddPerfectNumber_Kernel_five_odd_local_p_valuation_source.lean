-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_odd_local_p_valuation_source
-- name    : OddPerfectNumber.Kernel.five_odd_local_p_valuation_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T22:38:00.113269+00:00
-- url     : https://prove2.me/theorems/a35f5d96-63af-40c1-99db-74c1e2b36bed
-- title:
--   Some prime divisor carries an odd local p-valuation
-- statement:
--   Since the local p-valuations sum to exactly 5 (odd), some prime divisor t of m carries an odd local p-valuation. An odd valuation is positive, so p divides that local sigma factor: an actual odd-valuation incoming p-source in the residual. Proof: the proved valuation-sum identity plus finite-set parity (a sum of evens is even).
-- source:
--   Parity extraction from Proved five_p_valuation_sum_eq_five: 5 is odd, so not every summand is even. Gives the odd-valuation incoming p-source for 6eb10265.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem five_odd_local_p_valuation_source (p m s : Nat)
    (hp : p.Prime)
    (hm0 : m != 0)
    (hps : Not (Dvd.dvd p s))
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * s) :
    exists t : Nat, t ∈ m.primeFactors /\
      Not (Even (((∑ d ∈ (t ^ (2 * m.factorization t)).divisors, d).factorization) p)) := by
  sorry

end OddPerfectNumber.Kernel
