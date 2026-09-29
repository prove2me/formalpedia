-- Prove2me | Theorems.Thm_OddPerfectNumber_IsSquare_of_odd_pow_eq_one
-- name    : OddPerfectNumber.IsSquare_of_odd_pow_eq_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-11T10:43:10.715839+00:00
-- url     : https://prove2.me/theorems/59b00c3f-b4f4-4b1a-b905-44fbd26563ae
-- title:
--   Odd-order elements are squares
-- statement:
--   If $q^d = 1$ in $\mathbf{Z}/p$ for an odd exponent $d$, then $q$ is an explicit square: $q = (q^{(d+1)/2})^2$. In particular an element of odd multiplicative order is always a quadratic residue. This is the quadratic-residue step of the order analysis on the $k = 1$ distinguished prime.
-- source:
--   Valuation-flow analysis of the Odd Perfect Number Conjecture; Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)).

import Mathlib

namespace OddPerfectNumber

theorem IsSquare_of_odd_pow_eq_one {p q d : Nat} (hd : Odd d)
    (h : (q : ZMod p) ^ d = 1) : IsSquare (q : ZMod p) := by
  sorry

end OddPerfectNumber
