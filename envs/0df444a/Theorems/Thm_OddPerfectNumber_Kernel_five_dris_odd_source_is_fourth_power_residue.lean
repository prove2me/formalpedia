-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_dris_odd_source_is_fourth_power_residue
-- name    : OddPerfectNumber.Kernel.five_dris_odd_source_is_fourth_power_residue
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T12:11:59.152794+00:00
-- url     : https://prove2.me/theorems/3c72d5d6-c688-419c-afa3-ff4742be15f3
-- title:
--   The odd-multiplicity source of the Euler prime is a fourth power residue modulo p
-- statement:
--   Assume the two-prime square-free-index k=5 Dris residual: the Euler prime p is an odd prime congruent to 1 modulo 4 that does not divide m, the index is d1 squared times two distinct primes q and r, and both Dris equations hold. Then there is a prime t dividing m such that p divides the local geometric sum at t, p occurs in it to an odd multiplicity, and t is a fourth-power residue modulo p. This composes the proved odd-multiplicity source theorem with the proved fourth-power-residue theorem and is the formal basis for excluding any source that is a quadratic nonresidue modulo p.

import Mathlib

namespace OddPerfectNumber.Kernel

/-- In the two-prime k=5 residual the prime `t` supplied by
`five_dris_odd_multiplicity_p_source` (b860b1b5) is a FOURTH-POWER RESIDUE modulo `p`.

Concretely `(t : ZMod p) ^ ((p - 1) / 4) = 1`, which is exactly the statement accepted in
`sigma_source_of_p_is_fourth_power_residue` (6ff0e08d).  Composing the two Proved results
gives this child: the residual does not merely produce a source, it produces one whose
multiplicative order modulo `p` is ODD and divides `(p - 1) / 4`.

This is the formal form of the exclusion: since `p % 4 = 1`, an odd order dividing
`(p - 1) / 4` means `t` is a quadratic residue modulo `p`, so `t` cannot be the prime `3`
or any prime `l` with `(l / p) = -1`. -/
theorem five_dris_odd_source_is_fourth_power_residue (p m d1 q r : Nat) (hp : p.Prime)
    (hp2 : p != 2) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : Not (Dvd.dvd p m))
    (hq : q.Prime) (hr : r.Prime) (hqr : q < r)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r)))
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * (d1 ^ 2 * (q * r))) :
    exists t : Nat, t.Prime /\ Dvd.dvd t m /\
      Dvd.dvd p (∑ i ∈ Finset.range (2 * m.factorization t + 1), t ^ i) /\
      Not (Even ((∑ i ∈ Finset.range (2 * m.factorization t + 1), t ^ i).factorization p)) /\
      (t : ZMod p) ^ ((p - 1) / 4) = 1 := by
  sorry

end OddPerfectNumber.Kernel
