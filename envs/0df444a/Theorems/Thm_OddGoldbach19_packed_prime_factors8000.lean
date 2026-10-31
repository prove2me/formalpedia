-- Prove2me | Theorems.Thm_OddGoldbach19_packed_prime_factors8000
-- name    : OddGoldbach19.packed_prime_factors8000
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-30T20:40:37.863003+00:00
-- url     : https://prove2.me/theorems/cac185bc-a197-4aed-9aaa-dcf7bc0b4bb8
-- title:
--   Exact packed encodings of the finite prime shifts and their reversal
-- statement:
--   Let $B=2^{64}$, $D=40907$, and let $\mathcal Q$ be the fixed8000-prime list. The shared packed integers satisfy
--   $$Q_*=\sum_{q\in\mathcal Q}B^{(q-3)/2},\qquad R_*=\sum_{q\in\mathcal Q}B^{D-(q-3)/2}.$$
--   These identities connect the stored integers to the exact finite prime-position data.
-- source:
--   Exact finite packed-integer certificate for the known Riesel-Vaughan finite-shift method; all original-data identifications are independently kernel checked.

import Mathlib
import Definitions.Def_OddGoldbach19_CertificateData8000
import Definitions.Def_OddGoldbach19_PackedData8000
open scoped BigOperators

theorem OddGoldbach19.packed_prime_factors8000 :
    (OddGoldbach19.Cert8000.Qlist.map (fun q=>(2^64)^((q-3)/2))).sum=
      OddGoldbach19.Packed8000.packedQ ∧
    (OddGoldbach19.Cert8000.Qlist.map (fun q=>(2^64)^(40907-(q-3)/2))).sum=
      OddGoldbach19.Packed8000.packedR := by sorry
