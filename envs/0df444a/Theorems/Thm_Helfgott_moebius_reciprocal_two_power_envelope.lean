-- Prove2me | Theorems.Thm_Helfgott_moebius_reciprocal_two_power_envelope
-- name    : Helfgott.moebius_reciprocal_two_power_envelope
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T04:38:20.7771+00:00
-- url     : https://prove2.me/theorems/bcce704f-02b1-4985-8b63-c5ea63457812
-- title:
--   Combined finite square-root and logarithmic reciprocal Mobius envelope
-- statement:
--   Write $m(t)=\sum_{1\le n\le\lfloor t\rfloor}\mu(n)/n$. Let $11815\le T\le X$, $0\le\beta\le1/2$ and $\delta\ge1/\log T$. Assume $t\,m(t)^2\le2$ for every $1\le t<T$, and $|m(t)|\le0.03/\log t$ for every $t\ge11815$. Then for all $1\le t\le X$, $$|m(t)|\le(2/t)^\beta+\frac{0.03}{\log X}(X/t)^\delta.$$ The two stated cancellation estimates remain explicit inputs; the logarithmic comparison, floor endpoint at 1 and all real-power inequalities are proved.
-- source:
--   Original exact floor and log-power comparison adapting the two-part envelope in Helfgott, Minor arcs for Goldbach, equation (4.26). Written by Codex.

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
open Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott
theorem moebius_reciprocal_two_power_envelope
    (T X beta delta : ℝ) (hT : 11815 ≤ T) (hX : T ≤ X)
    (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1/2) (hd : 1/Real.log T ≤ delta)
    (hsqrt : ∀ t : ℝ, 1 ≤ t → t < T →
      (∑ n∈Icc 1 ⌊t⌋₊, ((moebius n : ℤ) : ℝ)/(n : ℝ))^2*t ≤ 2)
    (hdecay : ∀ t : ℝ, 11815 ≤ t →
      |∑ n∈Icc 1 ⌊t⌋₊, ((moebius n : ℤ) : ℝ)/(n : ℝ)| ≤ (3/100)/Real.log t) :
    ∀ t : ℝ, 1 ≤ t → t ≤ X →
      |∑ n∈Icc 1 ⌊t⌋₊, ((moebius n : ℤ) : ℝ)/(n : ℝ)| ≤
        (2/t)^beta + ((3/100)/Real.log X)*(X/t)^delta := by sorry
end Helfgott
