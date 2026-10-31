-- Prove2me | Theorems.Thm_OddGoldbach19_packed_weight_factor8000
-- name    : OddGoldbach19.packed_weight_factor8000
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-30T20:40:04.078411+00:00
-- url     : https://prove2.me/theorems/a1cd466c-ca17-4885-9aa1-a70baec8d347
-- title:
--   An exact packed encoding of the reversed singular-weight lookup table
-- statement:
--   Let $B=2^{64}$, $D=40907$, and let $\widehat W$ be the fixed half-difference lookup table. The shared packed integer satisfies
--   $$W_*=\sum_{d=1}^{D}\widehat W(d)B^{D-d}.$$
--   This identity connects the stored integer to the exact finite singular-weight data used by the convolution certificate.
-- source:
--   Exact finite packed-integer certificate for the known Riesel-Vaughan finite-shift method; all original-data identifications are independently kernel checked.

import Mathlib
import Definitions.Def_OddGoldbach19_CertificateData8000
import Definitions.Def_OddGoldbach19_PackedData8000
open scoped BigOperators

theorem OddGoldbach19.packed_weight_factor8000 :
    (∑ d∈Finset.Icc 1 40907,OddGoldbach19.Cert8000.WP d*(2^64)^(40907-d))=
      OddGoldbach19.Packed8000.packedW := by sorry
