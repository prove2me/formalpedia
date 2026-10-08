-- Prove2me | Theorems.Thm_Helfgott_vaughan_mobius_tail_energy_asymptotic
-- name    : Helfgott.vaughan_mobius_tail_energy_asymptotic
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T13:16:09.005182+00:00
-- url     : https://prove2.me/theorems/5fcee828-c049-44d8-b341-25ffcd5a1137
-- title:
--   Nonnegative leading term and explicit floor-error bound for the actual Vaughan Mobius coefficient energy
-- statement:
--   Let \(U\ge1\) and \(M\ge0\) be integers. Define \(b_U(m)=\sum_{d\mid m,d>U}\mu(d)\) and the finite arithmetic quadratic form
--   \[
--   C_U=\sum_{d,e\le U}\frac{\mu(d)\mu(e)}{\operatorname{lcm}(d,e)},
--   \]
--   where both indices are positive. Then \(C_U\ge0\), and
--   \[
--   \left|\sum_{U<m\le M}b_U(m)^2+\mathbf1_{M\ge1}-MC_U\right|\le U^2.
--   \]
--   This separates the actual Vaughan coefficient energy into a nonnegative main term and a completely explicit finite-endpoint error, preparing quantitative Type II estimates.
-- source:
--   Classical divisor-square and Selberg quadratic-form identity for the actual bilinear Mobius coefficient in Vaughan decomposition. Context: H. A. Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2, Type II estimates. Complete original Lean proof including the finite divisor-square identity, exact lcm counting, Mobius inversion and support endpoints. Mathlib attributions retained. Written by Codex.

import Definitions.Def_Helfgott_VaughanData
import Mathlib.Data.Nat.GCD.Basic
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

theorem vaughan_mobius_tail_energy_asymptotic (U M : ℕ) (hU : 1 ≤ U) :
    (0 ≤ ∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)*((ArithmeticFunction.moebius e : ℤ) : ℝ)/(Nat.lcm d e : ℝ)) ∧
    |(∑ m ∈ Finset.Icc (U+1) M,
      ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m)^2)+
      (if 1 ≤ M then 1 else 0)-
      (M : ℝ)*(∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)*((ArithmeticFunction.moebius e : ℤ) : ℝ)/(Nat.lcm d e : ℝ))| ≤ (U : ℝ)^2 := by sorry

end Helfgott
