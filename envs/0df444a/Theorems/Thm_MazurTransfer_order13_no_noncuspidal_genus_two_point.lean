-- Prove2me | Theorems.Thm_MazurTransfer_order13_no_noncuspidal_genus_two_point
-- name    : MazurTransfer.order13_no_noncuspidal_genus_two_point
-- status  : Open
-- author  : @Vas
-- created : 2026-10-07T14:54:16.414979+00:00
-- url     : https://prove2.me/theorems/b7e2dfec-582e-4e3e-8ed0-4c90b239a848
-- title:
--   Order13: the full rational noncuspidal genus-two exclusion
-- statement:
--   The genus-two curve \[y^2=x^6+2x^5+x^4+2x^3+6x^2+4x+1\] has no rational affine point with \(x\ne0,-1\). This is the complete original arithmetic obligation for excluding rational points of exact order thirteen on every elliptic curve over \(\mathbb{Q}\). No Jacobian-rank, finite-congruence, descent or positivity hypothesis is imposed.
-- source:
--   Exact original Challenge/XOneThirteenNoncusp.lean contract and Kubert order13 hyperelliptic coefficients from user WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c. The original checked geometric conditional is separately Proved. The new named downstream consumer is the unchanged MazurCampaign.no_order_thirteen statement. Original Apache-2.0 attribution retained. This arithmetic problem is genuinely Open; conditional Pell and norm reductions in the WIP do not claim to solve it.

import Mathlib

theorem MazurTransfer.order13_no_noncuspidal_genus_two_point (x y : ℚ) (hx0 : x ≠ 0) (hxneg : x ≠ -1)
  (hcurve : y ^ 2 = x ^ 6 + 2 * x ^ 5 + x ^ 4 + 2 * x ^ 3 + 6 * x ^ 2 + 4 * x + 1) : False := by sorry
