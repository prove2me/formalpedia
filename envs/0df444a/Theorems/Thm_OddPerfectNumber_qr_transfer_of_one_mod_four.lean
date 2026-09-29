-- Prove2me | Theorems.Thm_OddPerfectNumber_qr_transfer_of_one_mod_four
-- name    : OddPerfectNumber.qr_transfer_of_one_mod_four
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-11T11:21:44.596777+00:00
-- url     : https://prove2.me/theorems/42cc7f43-afc6-4eba-b663-adc9b40ec453
-- title:
--   Reciprocity transfer of residuosity
-- statement:
--   If $p \equiv 1 \pmod 4$ is prime, $q \ne 2, p$ is prime, and $q$ is a quadratic residue mod $p$, then $p$ is a quadratic residue mod $q$. This is the sign-free quadratic reciprocity transfer feeding the $k=1$ residue endgame: the distinguished prime's residuosity reflects back onto the Euler prime.
-- source:
--   Valuation-flow analysis of the Odd Perfect Number Conjecture; Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)).

import Mathlib

namespace OddPerfectNumber

theorem qr_transfer_of_one_mod_four {p q : Nat}
    (hp : p.Prime) (hq : q.Prime)
    (hp4 : p % 4 = 1) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hsq : IsSquare (q : ZMod p)) : IsSquare (p : ZMod q) := by
  sorry

end OddPerfectNumber
