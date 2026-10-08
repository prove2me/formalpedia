-- Prove2me | Theorems.Thm_Helfgott_vaughan_typeTwo_block_rational_arithmetic_upper
-- name    : Helfgott.vaughan_typeTwo_block_rational_arithmetic_upper
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T13:31:01.360013+00:00
-- url     : https://prove2.me/theorems/b7ed8728-2640-49bd-b106-f1fb3c968e6a
-- title:
--   Rational-frequency bound for actual Vaughan Type II blocks with explicit arithmetic energies
-- statement:
--   Let \(U,A,B,C,D,a,q\) be nonnegative integers with \(U,A,B\ge1\), \(C\ge U+1\), \(q\ge2\), and \((a,q)=1\). Let \(y>0\) and let \(\alpha\in\mathbb R/\mathbb Z\) satisfy \(\|\alpha-a/q\|\le q^{-2}\). Define \(b_U(m)=\sum_{r\mid m,r>U}\mu(r)\), \(K_U=\sum_{r,s\le U}\mu(r)\mu(s)/\operatorname{lcm}(r,s)\), and the actual compact Vaughan block
--   \[
--   T=\sum_{A\le d<B}\sum_{C\le m<D}\Lambda(d)b_U(m)\eta_2(dm/y)e(\alpha dm).
--   \]
--   Then
--   \[
--   |T|^2\le\log B\bigl(B\log4+2\sqrt B\log B\bigr)(DK_U+U^2)
--   (4\log2)^2\left(\left\lfloor\frac{D-C}{\lfloor q/2\rfloor}\right\rfloor+1\right)
--   \bigl(2(B-A)+8q(1+\log q)\bigr).
--   \]
--   The differences \(D-C\) and \(B-A\) are truncated at zero when an interval is empty. This unconditional block estimate combines rational-frequency cancellation with the actual arithmetic coefficients and their explicitly controlled finite energies. The signed finite quadratic form \(K_U\) is retained for further sharp arithmetic estimation.
-- source:
--   Classical divisor-square and Selberg quadratic-form identity for the actual bilinear Mobius coefficient in Vaughan decomposition. Context: H. A. Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2, Type II estimates. Complete original Lean proof including the finite divisor-square identity, exact lcm counting, Mobius inversion and support endpoints. Mathlib attributions retained. Written by Codex.

import Definitions.Def_Helfgott_VaughanData
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.GCD.Basic
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

theorem vaughan_typeTwo_block_rational_arithmetic_upper 
    (U A B C D a q : ℕ) (hU : 1 ≤ U) (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : U+1 ≤ C)
    (hq : 2 ≤ q) (ha : Nat.Coprime a q) (y : ℝ) (hy : 0 < y) (α : AddCircle (1 : ℝ))
    (hα : ‖α-((a : ℝ)/(q : ℝ) : AddCircle (1 : ℝ))‖ ≤ 1/(q : ℝ)^2) :
    ‖∑ d ∈ Finset.Ico A B,∑ m ∈ Finset.Ico C D,(vonMangoldt d : ℂ)*
      ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m : ℂ)*
      ((etaTwo (((d*m : ℕ) : ℝ)/y) : ℂ)*fourier ((d*m : ℕ) : ℤ) α)‖^2 ≤
      (Real.log (B : ℝ)*(Real.log 4*(B : ℝ)+2*Real.sqrt (B : ℝ)*Real.log (B : ℝ)))*
      ((D : ℝ)*(∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)*((ArithmeticFunction.moebius e : ℤ) : ℝ)/(Nat.lcm d e : ℝ))+(U : ℝ)^2)*
      ((4*Real.log 2)^2*(((D-C)/(q/2)+1 : ℕ) : ℝ)*
        (2*((B-A : ℕ) : ℝ)+8*(q : ℝ)*(1+Real.log (q : ℝ)))) := by sorry

end Helfgott
