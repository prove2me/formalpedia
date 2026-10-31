-- Prove2me | Theorems.Thm_OddGoldbach19_prime_family8000
-- name    : OddGoldbach19.prime_family8000
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-30T19:26:56.74193+00:00
-- url     : https://prove2.me/theorems/c44bbae6-0083-4933-a2d3-92b3d4c71fcd
-- title:
--   An exact family of8000 distinct odd prime shifts
-- statement:
--   Let $Q$ be the list of the first8000 odd primes supplied by the shared finite data. The list has no repetitions, has length8000, and every entry $p$ satisfies
--   $$p\text{ is prime},\qquad p\ne2,\qquad p\le81817.$$
--   These finite properties provide the prime shifts and their cardinality for a second moment argument. The separate weight-table and pair-sum certificates are not asserted here.
-- source:
--   Exact finite certificate for a Riesel-Vaughan prime-shift argument. The finite-family proof structure is adapted from public Apache2.0 Prove2Me accepted proof2e6ffca0-db78-43ae-93a9-bc1793b1bf07; the present family has8000 shifts through81817.

import Definitions.Def_OddGoldbach19_CertificateData8000

theorem OddGoldbach19.prime_family8000 :
    (∀ p∈OddGoldbach19.Cert8000.Qlist, p.Prime ∧ p≠2 ∧ p≤81817) ∧
    OddGoldbach19.Cert8000.Qlist.Nodup ∧ OddGoldbach19.Cert8000.Qlist.length=8000 := by sorry
