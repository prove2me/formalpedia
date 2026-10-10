-- Prove2me | Theorems.Thm_IntMul_DigitConvolution_digit_convolution_spec
-- name    : IntMul.DigitConvolution.digit_convolution_spec
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T08:45:44.876353+00:00
-- url     : https://prove2.me/theorems/4c6e3052-64aa-4910-aa0d-0c0f3356cfec
-- title:
--   Exact binary block polynomial and convolution with sharp coefficient growth bound
-- statement:
--   For every positive block width B and arbitrary campaign-model binary words x,y, the least-significant B-bit chunk polynomials evaluate at base 2^B to val(x), val(y), and their integer product. Every coefficient is exactly its chunk value and is less than 2^B, including all indices past the retained block count. Product coefficients satisfy the explicit finite convolution formula and are at most min(ceil(|x|/B),ceil(|y|/B))*(2^B-1)^2. Empty inputs, leading zeros, over-width B and a short high block are included. This proves exact encoding and coefficient growth before carry recovery; it is independent of an approximate transform or a particular machine implementation.
-- source:
--   Original exact binary-block/convolution interface in the campaign word model supporting HvdH multiplication. All binary-value helpers and encoding proofs are owned in the checked upload. Written by Codex.

import Definitions.Def_IntMul_DigitConvolution
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic

open IntMul IntMul.DigitConvolution

theorem IntMul.DigitConvolution.digit_convolution_spec (B : ℕ) (hB : 0 < B) (x y : List Bool) :
    (polynomial B x).eval (2^B)=val x ∧
    (polynomial B y).eval (2^B)=val y ∧
    (polynomial B x*polynomial B y).eval (2^B)=val x*val y ∧
    (∀ j, (polynomial B x).coeff j=digit B x j ∧ digit B x j < 2^B) ∧
    (∀ j, (polynomial B y).coeff j=digit B y j ∧ digit B y j < 2^B) ∧
    (∀ k,
      (polynomial B x*polynomial B y).coeff k=
        ∑ i ∈ Finset.range (blockCount B x),
          if i ≤ k then digit B x i*digit B y (k-i) else 0) ∧
    (∀ k, (polynomial B x*polynomial B y).coeff k ≤
      min (blockCount B x) (blockCount B y)*(2^B-1)^2) := by sorry
