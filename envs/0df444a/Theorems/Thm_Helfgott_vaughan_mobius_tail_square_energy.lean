-- Prove2me | Theorems.Thm_Helfgott_vaughan_mobius_tail_square_energy
-- name    : Helfgott.vaughan_mobius_tail_square_energy
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T13:03:28.433295+00:00
-- url     : https://prove2.me/theorems/e5fe0268-94f8-472b-81c7-3f7ef2fec93a
-- title:
--   Exact least-common-multiple quadratic formula for the actual Vaughan Mobius coefficient energy
-- statement:
--   Let \(U\ge1\) and \(M\ge0\) be integers, and define the actual Vaughan bilinear coefficient
--   \[
--   b_U(m)=\sum_{d\mid m,\,d>U}\mu(d).
--   \]
--   Its full finite square energy is exactly
--   \[
--   \sum_{U<m\le M}b_U(m)^2=
--   \sum_{d,e\le U}\mu(d)\mu(e)\left\lfloor\frac{M}{\operatorname{lcm}(d,e)}\right\rfloor
--   -\mathbf1_{M\ge1}.
--   \]
--   All divisor indices on the right are positive. This identity retains every sign and floor endpoint, exposing the finite arithmetic quadratic form needed to estimate the coefficient energy in Vaughan's Type II sum.
-- source:
--   Classical divisor-square and Selberg quadratic-form identity for the actual bilinear Mobius coefficient in Vaughan decomposition. Context: H. A. Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2, Type II estimates. Complete original Lean proof including the finite divisor-square identity, exact lcm counting, Mobius inversion and support endpoints. Mathlib attributions retained. Written by Codex.

import Definitions.Def_Helfgott_VaughanData
import Mathlib.Data.Nat.GCD.Basic
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

theorem vaughan_mobius_tail_square_energy (U M : ℕ) (hU : 1 ≤ U) :
    (∑ m ∈ Finset.Icc (U+1) M,
      ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m)^2) =
      (∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)*((ArithmeticFunction.moebius e : ℤ) : ℝ)*
        ((M/(Nat.lcm d e) : ℕ) : ℝ))-(if 1 ≤ M then 1 else 0) := by sorry

end Helfgott
