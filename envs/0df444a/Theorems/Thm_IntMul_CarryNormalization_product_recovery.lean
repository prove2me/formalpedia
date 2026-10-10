-- Prove2me | Theorems.Thm_IntMul_CarryNormalization_product_recovery
-- name    : IntMul.CarryNormalization.product_recovery
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T09:03:51.115231+00:00
-- url     : https://prove2.me/theorems/6a88b2b4-ccec-4d0f-89b8-0585885f3c41
-- title:
--   Exact convolution carry recovery with bounded intermediate bit widths
-- statement:
--   For every positive binary block width B and arbitrary campaign-model binary words x,y, one pure low-to-high carry pass through their exact digit-product coefficients recovers the canonical binary integer product padded to B*(ceil(|x|/B)+ceil(|y|/B)) bits. The final carry is zero and every emitted digit is below 2^B. With m=min(ceil(|x|/B),ceil(|y|/B)), every prefix carry is at most m*(2^B-1) and fits B+clog_2(m) bits; every coefficient-plus-carry sum fits 2B+clog_2(m) bits. Empty inputs, leading zeros, short high blocks and over-width B are included. This supplies exact arithmetic and finite width bounds for carry implementation; no physical machine cost is asserted.
-- source:
--   Original exact bounded-carry recovery for the campaign word model and HvdH multiplication. Binary-value helpers and all recovery proofs are owned in the upload; the accepted digit-convolution theorem supplies encoding and coefficient growth. Written by Codex.

import Definitions.Def_IntMul_CarryNormalization
import Theorems.Thm_IntMul_DigitConvolution_digit_convolution_spec
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic

open IntMul IntMul.CarryNormalization

theorem IntMul.CarryNormalization.product_recovery (B : ℕ) (hB : 0 < B) (x y : List Bool) :
    productWord B x y=bin
      (B*(DigitConvolution.blockCount B x+DigitConvolution.blockCount B y)) (val x*val y) ∧
    (scan (2^B) (coefficients B x y) 0).2=0 ∧
    (∀ d ∈ (scan (2^B) (coefficients B x y) 0).1, d < 2^B) ∧
    (∀ j, carryAt (2^B) (coefficients B x y) 0 j ≤
      min (DigitConvolution.blockCount B x) (DigitConvolution.blockCount B y)*(2^B-1) ∧
      carryAt (2^B) (coefficients B x y) 0 j <
        2^(B+Nat.clog 2 (min (DigitConvolution.blockCount B x) (DigitConvolution.blockCount B y)))) ∧
    (∀ a ∈ coefficients B x y, ∀ j,
      a+carryAt (2^B) (coefficients B x y) 0 j <
        2^(2*B+Nat.clog 2 (min (DigitConvolution.blockCount B x) (DigitConvolution.blockCount B y)))) := by sorry
