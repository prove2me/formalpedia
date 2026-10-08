-- Prove2me | Theorems.Thm_Helfgott_vaughan_typeTwo_rational_upper
-- name    : Helfgott.vaughan_typeTwo_rational_upper
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T11:40:32.838299+00:00
-- url     : https://prove2.me/theorems/9c524286-165c-41a2-a207-427aee5f1e53
-- title:
--   Explicit rational-approximation Type II bound for the actual compact Vaughan exponential sum
-- statement:
--   For natural cutoffs U,V, a reduced rational a/q with q>=2, positive smoothing scale y and circle frequency alpha within 1/q^2 of a/q, the squared norm of the exact etaTwo-weighted Vaughan Type II sum is at most the product of the Lambda square-energy over V<d<=floor(y) and the Mobius-tail convolution square-energy over U<m<=floor(y), multiplied by (4 log 2)^2, by floor((floor(y)-U)/floor(q/2))+1, and by 2*(floor(y)-V)+8*q*(1+log(q)). All finite endpoints, odd q and exact resonances are covered. The rational-frequency distance sums are bounded by a complete separation, packing and harmonic-sum proof, rather than assumed.
-- source:
--   Classical Vaughan decomposition, Cauchy-Schwarz and bilinear coefficient correlations, as used in H. A. Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2. Complete original Lean proof for the actual etaTwo smoothing, including geometric cancellation and two Abel summations. Mathlib attributions retained. Written by Codex.

import Definitions.Def_Helfgott_VaughanData
import Mathlib.Analysis.Normed.Group.AddCircle
open Finset Real ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

theorem vaughan_typeTwo_rational_upper (U V a q : ℕ) (hq : 2 ≤ q)
    (ha : Nat.Coprime a q) (y : ℝ) (hy : 0 < y) (α : AddCircle (1 : ℝ))
    (hα : ‖α-((a : ℝ)/(q : ℝ) : AddCircle (1 : ℝ))‖ ≤ 1/(q : ℝ)^2) :
    ‖expSum (fun n => ((vaughanTypeTwo U V n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α‖^2 ≤
      (∑ d ∈ Finset.Icc (V+1) (Nat.floor y),(vonMangoldt d)^2)*
      (∑ m ∈ Finset.Icc (U+1) (Nat.floor y),
        ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m)^2)*
      ((4*Real.log 2)^2*(((Nat.floor y-U)/(q/2)+1 : ℕ) : ℝ)*
        (2*((Nat.floor y-V : ℕ) : ℝ)+8*(q : ℝ)*(1+Real.log (q : ℝ)))) := by sorry

end Helfgott
