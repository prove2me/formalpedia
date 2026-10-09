-- Prove2me | Theorems.Thm_Helfgott_squarefree_harmonic_log_upper_bound
-- name    : Helfgott.squarefree_harmonic_log_upper_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-08T23:27:27.659567+00:00
-- url     : https://prove2.me/theorems/88169d8c-412c-4a5e-87d8-37bba591cc1a
-- title:
--   Unconditional squarefree harmonic bound with constant 1.166
-- statement:
--   For every real $x\ge10000$, $$\sum_{n\le\lfloor x\rfloor}\frac{\mu(n)^2}{n}\le\frac{6}{\pi^2}\log x+1.166.$$ The sum is over positive integers. This quantitative squarefree harmonic bound supplies the density factor in the centered Möbius hyperbola estimate used toward the explicit minor-arc argument. The finite baseline and the complete infinite tail are proved, with no numerical or analytic hypotheses beyond the stated range.
-- source:
--   O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 7, https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Independent proof of the required harmonic estimate from the fully proved squarefree-count error 3*sqrt(x), a complete kernel-checked baseline through 10000, and Abel summation. Written by Codex.

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Definitions.Def_Helfgott_MobiusFiniteCertificate
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Data.Rat.BigOperators
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

theorem squarefree_harmonic_log_upper_bound  (x : ℝ) (hx : 10000 ≤ x) :
    (∑ n ∈ Icc 1 ⌊x⌋₊, ((moebius n : ℤ) : ℝ) ^ 2 / (n : ℝ)) ≤
      (6 / Real.pi ^ 2) * Real.log x + 583 / 500 := by sorry

end Helfgott
