-- Prove2me | Theorems.Thm_HypergraphUnreliability_FPRAS_lemma_7_1
-- name    : HypergraphUnreliability.FPRAS.lemma_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:14.610046+00:00
-- url     : https://prove2.me/theorems/3ad0b89e-f73a-4e5c-9a6e-4caf6f88fd8f
-- title:
--   Lemma 7.1 — Polynomial-time logarithm approximation
-- statement:
--   Let $A,B$ be integers with $0<A<B$, let $b$ be the binary length of $B$ (the fraction need not be reduced), and let $T=\log(B/A)$, $H_0=b+1$. For every positive rational $\eta$, a rational $T^\prime$ with
--   $$0\le T^\prime\le T<H_0,\qquad T-T^\prime\le\eta$$
--   can be computed in time polynomial in the encodings of $A,B,\eta$.
--
--   This is the one-sided rational approximation of a horizon or logarithmic rate, used in §7 and, per edge, in §9.1.
--
--   **Formalization Note** When $\eta<1$, $\log(1/\eta)$ is bounded by the encoding length of $\eta$, so the printed clause "and in $\log(1/\eta)$" is contained in the encoding length.
--
--   Differences from the source:
--   - encoding: polynomial time in the bit model → one fixed Mathlib `Turing.FinTM2` with finite alphabets and one fixed polynomial bounding its steps, chosen before the inputs; reason: a `FinTM2` step executes a bounded program fragment on a finite alphabet, so steps and bit operations agree up to a constant factor; every instance of the claim is kept
-- source:
--   Zhijie Zheng, STOC 2027 submission #37 (October 2026), Lemma 7.1, p. 8; context §7, p. 8

import Mathlib
import Definitions.Def_HypergraphUnreliability_FPRAS_Instance

noncomputable section

open scoped BigOperators Classical

namespace HypergraphUnreliability.FPRAS


/-- Lemma 7.1, p. 8. With `T = log(B/A)` and `H₀ = b + 1`, `b` the binary length of `B`, a rational
`T′` with `0 ≤ T′ ≤ T < H₀` and `T - T′ ≤ η` is computable in time polynomial in the encoding of
`A, B, η` (which bounds `log(1/η)` when `η < 1`). -/
theorem lemma_7_1 :
    ∃ f : LogInput → Frac,
      (∀ x : LogInput, 0 < x.A → x.A < x.B → 0 < x.η.num → 0 < x.η.den →
        0 < (f x).den ∧
        0 ≤ (((f x).val : ℚ) : ℝ) ∧
        (((f x).val : ℚ) : ℝ) ≤ Real.log ((x.B : ℝ) / x.A) ∧
        Real.log ((x.B : ℝ) / x.A) < ((Nat.size x.B + 1 : ℕ) : ℝ) ∧
        Real.log ((x.B : ℝ) / x.A) - (((f x).val : ℚ) : ℝ) ≤ ((x.η.val : ℚ) : ℝ)) ∧
      PolyComputesIn (fun x : LogInput => 0 < x.A ∧ x.A < x.B ∧ 0 < x.η.num ∧ 0 < x.η.den)
        LogInput.encode (fun x => fracCode (f x)) (fun x => x.encode.length) := by sorry

end HypergraphUnreliability.FPRAS
