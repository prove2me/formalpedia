-- Prove2me | Theorems.Thm_Helfgott_cdem_mertens4345_tail_of_finite_sources
-- name    : Helfgott.cdem_mertens4345_tail_of_finite_sources
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T02:53:41.63898+00:00
-- url     : https://prove2.me/theorems/9ecbb205-c051-41bc-84bd-6d66a1f31b59
-- title:
--   CDEM Mertens tail from five bounded computation certificates
-- statement:
--   Let $\mu$ be the Mobius function, $M(n)=\sum_{1\le d\le n}\mu(d)$ and $Q(y)=\sum_{1\le d\le y}|\mu(d)|$. Put $K=199330$, $N=5\times10^9$, $T=10^{16}$, $G(0)=0$ and $G(k)=|1-\sum_{d=1}^{K}\mu(d)\lfloor k/d\rfloor|$ for $k\ge1$. Assume the five bounded inputs
--   $$\sum_{k=1}^{N}\frac{G(k)-G(k-1)}k\le\frac{324880457633740}{10^{18}},\qquad
--   \sum_{k=1}^{N}\frac{|G(k)-G(k-1)|}{\sqrt{k}}\le\frac{48710223109607260068028}{10^{18}},$$
--   $$|M(n)|\le0.571\sqrt n\quad(80000\le n\le T),$$
--   $$\left|Q(y)-\frac6{\pi^2}y\right|\le0.0755\sqrt y\quad(9243<y\le T),\qquad
--   \left|Q(y)-\frac6{\pi^2}y\right|\le0.0285\sqrt y\quad(438429<y\le T).$$
--   Then every integer $X\ge T$ satisfies
--   $$|M(X)|\le\frac X{4345}.$$
--   The actual prefix constants, all unbounded analytic steps, finite weights, scalar endpoints and monotonicity are proved in the supporting argument. No prior unbounded Mertens or squarefree estimate is an assumption. The five bounded computation obligations themselves remain assumptions of this theorem.
-- source:
--   Cohen–Dress–El Marraki bootstrap, adapted from Gershon Bialer, gersh/ternary-goldbach-lean, Apache 2.0, pinned commit 27df23af6a712895f22204d0d81102baa74f0ebe. The exact Mobius convolution, density, floor identities and actual prefix are independently proved from Mathlib and kernel-checked arithmetic here. No PrimeNumberTheoremAnd import or historical source axiom is used. Written by Codex.

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.BigOperators.Intervals
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

theorem cdem_mertens4345_tail_of_finite_sources
    (hU : let G : ℕ → ℝ := fun k => if k = 0 then 0 else
        |1 - ∑ d ∈ Icc 1 199330, (moebius d : ℝ)*((k/d : ℕ) : ℝ)|
      (∑ k ∈ Icc 1 5000000000, (G k-G (k-1))/(k : ℝ)) ≤
        (324880457633740 / 1000000000000000000 : ℝ))
    (hV : let G : ℕ → ℝ := fun k => if k = 0 then 0 else
        |1 - ∑ d ∈ Icc 1 199330, (moebius d : ℝ)*((k/d : ℕ) : ℝ)|
      (∑ k ∈ Icc 1 5000000000, |G k-G (k-1)|/Real.sqrt k) ≤
        (48710223109607260068028 / 1000000000000000000 : ℝ))

    (hHurst : ∀ k : ℕ, 80000 ≤ k → k ≤ 10 ^ 16 →
      |∑ d ∈ Icc 1 k, (moebius d : ℝ)| ≤ (571/1000 : ℝ)*Real.sqrt k)
    (hQhead1 : ∀ y : ℝ, 9243 < y → y ≤ (10000000000000000 : ℝ) →
      |(∑ d ∈ Icc 1 ⌊y⌋₊, |(moebius d : ℝ)|) - (6/Real.pi^2)*y| ≤
        (755/10000 : ℝ)*Real.sqrt y)
    (hQhead2 : ∀ y : ℝ, 438429 < y → y ≤ (10000000000000000 : ℝ) →
      |(∑ d ∈ Icc 1 ⌊y⌋₊, |(moebius d : ℝ)|) - (6/Real.pi^2)*y| ≤
        (285/10000 : ℝ)*Real.sqrt y)
    (X : ℕ) (hX : 10000000000000000 ≤ X) :
    |∑ d ∈ Icc 1 X, (moebius d : ℝ)| ≤ (X : ℝ)/4345 := by sorry

end Helfgott
