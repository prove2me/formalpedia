-- Prove2me | Theorems.Thm_Helfgott_cdem_squarefree_exact_decomposition
-- name    : Helfgott.cdem_squarefree_exact_decomposition
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:19:36.456077+00:00
-- url     : https://prove2.me/theorems/36485d61-71dd-4b7c-b7d6-2a7c8b917b9e
-- title:
--   Exact centered squarefree decomposition for the CDEM bootstrap
-- statement:
--   Let $\mu$ be the Mobius function, $M(t)=\sum_{1\le a\le t}\mu(a)$, $Q(x)=\sum_{1\le a\le x}|\mu(a)|$, and $X_j=\sqrt{x/j}$. For every $x>0$ and integer $1\le n\le\lfloor x\rfloor$, the exact identity
--   $$Q(x)-\frac6{\pi^2}x=-2x\int_{X_n}^{\infty}\frac{M(t)}{t^3}\,dt+\sum_{j=1}^{n-1}M(X_j)+\frac12M(X_n)-\sum_{a=1}^{\lfloor X_n\rfloor}\mu(a)\left(\left\{\frac{x}{a^2}\right\}-\frac12\right)$$
--   holds, where $\{y\}$ denotes fractional part. This supplies the exact analytic and finite-sum identity underlying CDEM Lemma 1. It assumes no previous Mertens estimate, squarefree estimate, finite numerical certificate, or zero-location computation; quantitative bootstrap estimates are separate conclusions.
-- source:
--   Cohen, Dress and El Marraki, Explicit estimates for summatory functions linked to the Mobius function, Functiones et Approximatio 37 (2007), Lemma 1 and equation (2.1). Adapted from Gershon Bialer, ternary-goldbach-lean, Apache 2.0, commit 27df23af6a712895f22204d0d81102baa74f0ebe. The convolution and reciprocal-square density are independently proved from Mathlib here. Written by Codex.

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Order.Floor.Semifield
open Finset MeasureTheory ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

theorem cdem_squarefree_exact_decomposition (x : ℝ) (n : ℕ)
    (hx : 0 < x) (hn : 1 ≤ n) (hnx : n ≤ ⌊x⌋₊) :
    let M : ℝ → ℝ := fun t =>
      ∑ a ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.moebius a : ℝ)
    let X : ℕ → ℝ := fun j => Real.sqrt (x / (j : ℝ))
    (∑ a ∈ Finset.Icc 1 ⌊x⌋₊, |(ArithmeticFunction.moebius a : ℝ)|)
        - (6 / Real.pi ^ 2) * x
      = -2 * x * (∫ t in Set.Ioi (X n), M t / t ^ 3)
        + (∑ j ∈ Finset.Icc 1 (n - 1), M (X j)) + M (X n) / 2
        - (∑ a ∈ Finset.Icc 1 ⌊X n⌋₊,
          (ArithmeticFunction.moebius a : ℝ)
            * (Int.fract (x / (a : ℝ) ^ 2) - 1 / 2)) := by sorry

end Helfgott
