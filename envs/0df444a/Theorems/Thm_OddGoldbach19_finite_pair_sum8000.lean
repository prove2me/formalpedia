-- Prove2me | Theorems.Thm_OddGoldbach19_finite_pair_sum8000
-- name    : OddGoldbach19.finite_pair_sum8000
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-30T20:49:29.809261+00:00
-- url     : https://prove2.me/theorems/3ea2d7bd-075b-4005-a94c-bc22c37d6af0
-- title:
--   An exact finite bound for the8000-shift rounded pair sum
-- statement:
--   Let $\mathcal Q$ be the shared list of8000 odd primes through81817, and let $\widehat W$ be the shared rounded half-difference lookup table. Then
--   $$\sum_{a\in\mathcal Q}\sum_{\substack{b\in\mathcal Q\\b<a}}\widehat W\!\left(\frac{a-b}{2}\right)\le557349373474.$$
--   After division by10000 this gives55,734,937.3474, below the55,737,000 bound used in the finite-shift second moment estimate.
-- source:
--   Exact finite-shift certificate for the Riesel-Vaughan prime-sum method, On sums of primes (1983). The computation is verified through packed natural-polynomial convolution, with separately checked original-data factor identities and an exact integer coefficient.

import Definitions.Def_OddGoldbach19_CertificateData8000

theorem OddGoldbach19.finite_pair_sum8000 :
    (OddGoldbach19.Cert8000.Qlist.map fun a=>(OddGoldbach19.Cert8000.Qlist.map fun b=>
      if b<a then OddGoldbach19.Cert8000.WP ((a-b)/2) else 0).sum).sum≤557349373474 := by sorry
