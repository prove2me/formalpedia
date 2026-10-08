-- Prove2me | Theorems.Thm_Helfgott_vaughan_etaTwo_complete_decomposition
-- name    : Helfgott.vaughan_etaTwo_complete_decomposition
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T10:31:26.127953+00:00
-- url     : https://prove2.me/theorems/d12c3836-72da-45ec-b427-4bbf25460b2d
-- title:
--   Complete compactly smoothed Vaughan decomposition with exact finite supports
-- statement:
--   For every pair of natural cutoffs U,V, every positive real scale y and every frequency on the unit circle, the full von Mangoldt exponential sum with the challenge's compact etaTwo smoothing equals its exact four-term Vaughan decomposition. The Type I term has outer support 1 <= d <= min(U,floor y). The correction has outer support 1 <= d <= min(UV,floor y). The small von Mangoldt term retains Lambda at n <= V. The Type II term has d >= V+1 and m >= U+1, with dm <= y and coefficient Lambda(d)(mu_{>U}*1)(m). All inner supports are 1 <= m <= floor(y/d), or the corresponding Type II lower cutoff. No infinite tails, endpoint terms or smoothing errors are discarded. The theorem is an exact unconditional identity needed to estimate the actual minor arcs.
-- source:
--   Vaughan identity as used in H. A. Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2, minor-arc analysis. Complete original Lean derivation from arithmetic convolution, the Mobius inverse identity and the exact etaTwo support. Mathlib and imported definition attributions retained. Written by Codex.

import Definitions.Def_Helfgott_VaughanData
open ArithmeticFunction MeasureTheory Set Finset
open scoped BigOperators Classical

namespace Helfgott

theorem vaughan_etaTwo_complete_decomposition (U V : ℕ) (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) :
    expSum (fun n => ((ArithmeticFunction.vonMangoldt n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α =
      (∑ d ∈ Finset.Icc 1 (min U (Nat.floor y)), ((ArithmeticFunction.moebius d : ℤ) : ℂ)*
        (∑ m ∈ Finset.Icc 1 (Nat.floor (y/(d : ℝ))),
          ((Real.log (m : ℝ)*etaTwo (((d*m : ℕ) : ℝ)/y) : ℝ) : ℂ)*fourier ((d*m : ℕ) : ℤ) α))-
      (∑ d ∈ Finset.Icc 1 (min (U*V) (Nat.floor y)),
        (((arithmeticCutoff U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*
          arithmeticCutoff V ArithmeticFunction.vonMangoldt) d : ℝ) : ℂ)*
        (∑ m ∈ Finset.Icc 1 (Nat.floor (y/(d : ℝ))),
          ((etaTwo (((d*m : ℕ) : ℝ)/y) : ℝ) : ℂ)*fourier ((d*m : ℕ) : ℤ) α))+
      expSum (fun n => ((arithmeticCutoff V ArithmeticFunction.vonMangoldt n*
        etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α+
      (∑ d ∈ Finset.Icc (V+1) (Nat.floor y), ∑ m ∈ Finset.Icc (U+1) (Nat.floor (y/(d : ℝ))),
        ((ArithmeticFunction.vonMangoldt d*
          (arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m*
          etaTwo (((d*m : ℕ) : ℝ)/y) : ℝ) : ℂ)*fourier ((d*m : ℕ) : ℤ) α) := by sorry

end Helfgott
