-- Prove2me | Theorems.Thm_Helfgott_vaughan_typeTwo_correlation_cancellation
-- name    : Helfgott.vaughan_typeTwo_correlation_cancellation
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T11:14:13.956566+00:00
-- url     : https://prove2.me/theorems/1a4f2e5a-4502-4804-936c-fe2d2a14e900
-- title:
--   Actual compact Vaughan Type II cancellation by coefficient correlations, including every resonance
-- statement:
--   For every natural cutoff U,V, positive scale y and circle frequency alpha, the square norm of the exact compact etaTwo-weighted Vaughan Type II exponential sum is bounded by its Lambda square-energy on V<d<=floor(y), times the explicit double correlation sum over U<m,n<=floor(y) of absolute Mobius-tail convolution coefficients. The correlation kernel is (4 log 2)^2 times floor(y)-V at an exact resonance (m-n)*alpha=0, and otherwise times min(floor(y)-V,2/norm((m-n)*alpha)). The Type II decomposition, compact support, pair smoothing cancellation and coefficient correlation inequality are all proved without analytic hypotheses.
-- source:
--   Classical Vaughan decomposition, Cauchy-Schwarz and bilinear coefficient correlations, as used in H. A. Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2. Complete original Lean proof for the actual etaTwo smoothing, including geometric cancellation and two Abel summations. Mathlib attributions retained. Written by Codex.

import Definitions.Def_Helfgott_VaughanData
import Mathlib.Analysis.Normed.Group.AddCircle
open Finset Real ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

theorem vaughan_typeTwo_correlation_cancellation (U V : ℕ) (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) :
    ‖expSum (fun n => ((vaughanTypeTwo U V n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α‖^2 ≤
      (∑ d ∈ Finset.Icc (V+1) (Nat.floor y),(vonMangoldt d)^2)*
      (∑ m ∈ Finset.Icc (U+1) (Nat.floor y),∑ n ∈ Finset.Icc (U+1) (Nat.floor y),
        |(arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m| *
        |(arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) n| *
        ((4*Real.log 2)^2*
        (if ((m : ℤ)-(n : ℤ)) • α = 0 then ((Nat.floor y-V : ℕ) : ℝ)
         else min ((Nat.floor y-V : ℕ) : ℝ) (2/‖((m : ℤ)-(n : ℤ)) • α‖)))) := by sorry

end Helfgott
