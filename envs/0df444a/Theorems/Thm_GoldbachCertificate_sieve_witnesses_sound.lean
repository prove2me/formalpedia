-- Prove2me | Theorems.Thm_GoldbachCertificate_sieve_witnesses_sound
-- name    : GoldbachCertificate.sieve_witnesses_sound
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T00:33:22.426544+00:00
-- url     : https://prove2.me/theorems/5d3bfe66-1631-43bb-b3a0-6adbf9956698
-- title:
--   Checked Goldbach certificates produce sieve witnesses on the whole block
-- statement:
--   A successfully checked consecutive-even Goldbach certificate can be used directly in the existing sieve-survivor interface. Let its first even integer be $2a$, its row count be $m$, and its left-prime bound be $s$. For an even $n$ with $2a\le n<2(a+m)$, an external sieve interval $[\ell,h]$ with $\ell\le\max(0,2a-s)$ and $n\le h$, and any cutoff $c$, the certificate supplies a small prime $p\le s$ and a survivor $q$ in that interval with $n=p+q$.
--
--   The certificate soundness proof first supplies actual primes. A prime $q$ is a survivor for every sieve cutoff: a prime divisor of $q$ must equal $q$, so the forbidden-small-divisor filter is empty. The sum and left-prime bound give the required lower interval bound, and $q\le n$ gives the upper bound. No dense survivor set is evaluated.
--
--   This bridge targets the existing `GoldbachSieve` witness format used by the Richstein finite-verification route. It proves an implication from checked certificates; it supplies no certificate for the full $4\cdot10^{14}$ range and assumes no prime-distribution estimate. Its local axiom closure contains only standard Lean foundations.
-- source:
--   Checkable computational certificates for the finite Goldbach input in https://arxiv.org/abs/1201.6656; method, exact coverage and performance evidence in the statement.

import Definitions.Def_GoldbachCertificate
import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
set_option autoImplicit false

theorem GoldbachCertificate.sieve_witnesses_sound (first smallBound lo hi cutoff : ℕ) (tree : GoldbachCertificate.PrimeTree)
    (rows : List (ℕ × ℕ)) (ht : tree.check = true)
    (hr : GoldbachCertificate.checkRows first smallBound tree rows = true)
    (hcover : lo ≤ 2 * first - smallBound)
    (n : ℕ) (hlo : 2 * first ≤ n) (hhi : n < 2 * (first + rows.length))
    (hnhi : n ≤ hi) (he : Even n) :
    ∃ p ∈ ((Finset.Icc 2 smallBound).filter Nat.Prime),
      ∃ q ∈ GoldbachSieve.survivors lo hi cutoff, n = p + q := by sorry
