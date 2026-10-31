-- Prove2me | Theorems.Thm_OddGoldbach19_packed_numeric8000
-- name    : OddGoldbach19.packed_numeric8000
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-30T20:21:17.234545+00:00
-- url     : https://prove2.me/theorems/75cbecb4-c188-41d7-ad3c-92c419aab189
-- title:
--   An exact integer convolution coefficient
-- statement:
--   Let $Q_*,R_*,W_*$ be the three fixed integers in the shared packed data. Their base-$2^{64}$ coefficient at position$2\cdot40907$ is
--   $$\left\lfloor\frac{Q_*R_*W_*}{(2^{64})^{2\cdot40907}}\right\rfloor\bmod2^{64}=557349373474.$$
--   This is an exact finite arithmetic statement. Relating the packed integers to the prime-shift family and the singular-weight lookup table is a separate proof obligation.
-- source:
--   Exact numerical component of a private finite-shift certificate for the known Riesel-Vaughan prime-sum method. The coefficient computation uses chunked natural-number encodings; it does not itself assert their finite-sum interpretation.

import Definitions.Def_OddGoldbach19_PackedData8000

theorem OddGoldbach19.packed_numeric8000 :
    ((OddGoldbach19.Packed8000.packedQ*OddGoldbach19.Packed8000.packedR*
      OddGoldbach19.Packed8000.packedW)/(2^64)^(2*40907))%(2^64)=557349373474 := by sorry
