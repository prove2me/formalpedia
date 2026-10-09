-- Prove2me | Theorems.Thm_Helfgott_moebius_reciprocal_all_from_five_finite_sources_and_prime_errors
-- name    : Helfgott.moebius_reciprocal_all_from_five_finite_sources_and_prime_errors
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T03:13:01.870977+00:00
-- url     : https://prove2.me/theorems/38b89cec-64fd-4860-adff-2d3cfb1589c9
-- title:
--   Full reciprocal Mobius estimate from five bounded certificates and two prime-error envelopes
-- statement:
--   Let $\mu$ be the Mobius function, $M(n)=\sum_{d=1}^n\mu(d)$, $Q(y)=\sum_{d\le\lfloor y\rfloor}|\mu(d)|$ and $\Lambda$ the von Mangoldt function. Put $K=199330$, $N=5\times10^9$, $T=10^{16}$, $G(0)=0$ and $G(k)=|1-\sum_{d=1}^K\mu(d)\lfloor k/d\rfloor|$ for $k\ge1$. Assume the five bounded certificates
--   $$\sum_{k=1}^N\frac{G(k)-G(k-1)}k\le\frac{324880457633740}{10^{18}},\qquad
--   \sum_{k=1}^N\frac{|G(k)-G(k-1)|}{\sqrt k}\le\frac{48710223109607260068028}{10^{18}},$$
--   $$|M(n)|\le0.571\sqrt n\quad(80000\le n\le T),$$
--   $$\left|Q(y)-\frac6{\pi^2}y\right|\le0.0755\sqrt y\quad(9243<y\le T),\qquad
--   \left|Q(y)-\frac6{\pi^2}y\right|\le0.0285\sqrt y\quad(438429<y\le T).$$
--   For a real $C$ with $|C|\le2$, set
--   $$A_C(u)=\sum_{k\le\lfloor u\rfloor}\big((\Lambda*\Lambda)(k)-\Lambda(k)\log k+C\big),$$
--   where $*$ is Dirichlet convolution. Assume also the two prime-error envelopes
--   $$|A_C(u)|\le0.031u\quad(21\times10^9\le u<T),\qquad |A_C(u)|\le0.0065u\quad(u\ge T).$$
--   Then every real $x\ge11815$ satisfies
--   $$\left|\sum_{d\le\lfloor x\rfloor}\frac{\mu(d)}d\right|\le\frac{0.03}{\log x}.$$
--   All finite-prefix, initial-integral, analytic-bootstrap, middle-range and high-tail conversions are discharged in the proof. The five bounded certificates and two prime-error envelopes remain assumptions. There is no remaining assumed reciprocal or unbounded Mertens estimate.
-- source:
--   Independent assembly of the CDEM bootstrap and corrected El Marraki/Ramare reciprocal conversion, with an accepted finite Mobius window. The CDEM analytic component adapts Gershon Bialer, gersh/ternary-goldbach-lean, Apache 2.0, pinned commit 27df23af6a712895f22204d0d81102baa74f0ebe. Written by Codex.

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.BigOperators.Intervals
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

theorem moebius_reciprocal_all_from_five_finite_sources_and_prime_errors
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
    (C : ℝ) (hC : |C| ≤ 2)
    (hRhigh : ∀ u : ℝ, 10000000000000000 ≤ u →
      |∑ k ∈ Icc 1 ⌊u⌋₊,
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| ≤
          (65 / 10000) * u)
    (hRmiddle : ∀ u : ℝ, 21000000000 ≤ u → u < 10000000000000000 →
      |∑ k ∈ Icc 1 ⌊u⌋₊,
        ((vonMangoldt * vonMangoldt) k - vonMangoldt k * Real.log (k : ℝ) + C)| ≤
          (31 / 1000) * u)
    (x : ℝ) (hx : 11815 ≤ x) :
    |∑ d ∈ Icc 1 ⌊x⌋₊, ((moebius d : ℤ) : ℝ) / (d : ℝ)| ≤
      (3 / 100) / Real.log x := by sorry

end Helfgott
