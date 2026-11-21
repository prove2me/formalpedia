-- Prove2me | Theorems.Thm_MasulloRH_prime_halfspace_relative_diagonal_mass
-- name    : MasulloRH.prime_halfspace_relative_diagonal_mass
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T03:08:42.914+00:00
-- url     : https://prove2.me/theorems/5c051c46-d090-4494-bb91-d0dd2da3f371
-- title:
--   The integrated prime half-space boundary has the local prime-power weights
-- statement:
--   Let $L=\log p$, $r=1/\sqrt p$. For the coefficients of $(1-rD^{-1})/(1-rD)$, put $K_{d,j}(u)=b_{j-d}b_j(1_{u\le(j-d)L}-1_{u\le-dL})$. For every integer lag $d$ the sum of the integrals of $|K_{d,j}|$ is finite. For every finite set of lags $T\subset\mathbf Z$ and complex function $f$, integrating the signed boundary against the samples $f(dL)$ yields exactly $L\sum_{0\ne d\in T}p^{-|d|/2} f(dL)$. This is the Lebesgue-integrated diagonal identity for the unramified chart cutoffs.
-- source:
--   Half-space trace comparison in the rational radial S-local model, extending the bilateral coefficient calculation https://prove2.me/theorems/034e9368-95e0-4502-b670-58bfdee4852c. Compare Masullo, Theorem 12.4.1.1, equation (12.4.1.3), and Connes, Trace formula in noncommutative geometry and the zeros of the Riemann zeta function, section VII.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open Set MeasureTheory Finset

theorem MasulloRH.prime_halfspace_relative_diagonal_mass (p : ℕ) (hp : p.Prime) (T : Finset ℤ) (f : ℝ → ℂ) :
    let L := Real.log p
    let r := 1/Real.sqrt p
    let b (j : ℤ) : ℝ := if j = -1 then -r else if 0 ≤ j then (1-r^2)*r^j.toNat else 0
    let K (d j : ℤ) (u : ℝ) := (b (j-d)*b j) *
      ((if u ≤ ((j:ℝ)-(d:ℝ))*L then (1:ℝ) else 0) - (if u ≤ -(d:ℝ)*L then 1 else 0))
    (∀ d, Summable (fun j => ∫ u : ℝ, |K d j u|)) ∧
    (∑ d ∈ T, (Complex.ofReal (∫ u : ℝ, ∑' j : ℤ, K d j u)) * f ((d:ℝ)*L)) =
      (L:ℂ) * ∑ d ∈ T, (if d=0 then 0 else (r^d.natAbs:ℝ):ℂ) * f ((d:ℝ)*L) := by sorry
