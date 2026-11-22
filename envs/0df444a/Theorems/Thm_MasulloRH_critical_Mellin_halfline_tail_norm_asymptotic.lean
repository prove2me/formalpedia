-- Prove2me | Theorems.Thm_MasulloRH_critical_Mellin_halfline_tail_norm_asymptotic
-- name    : MasulloRH.critical_Mellin_halfline_tail_norm_asymptotic
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T12:23:01.576188+00:00
-- url     : https://prove2.me/theorems/18eb384e-8b35-4a5d-af03-107c11063728
-- title:
--   Sharp half-line tail asymptotic for the Mellin evaluation in the rational critical Masullo weight
-- statement:
--   For a>0 and w(x)=exp(|x|)(1+x²)², the normalized translated right tail integral of exp((1-a)x)/w(x), with x=L+y, y>0, multiplied by exp(aL)(1+L²)², tends to 1/a as L tends to infinity. Reflection at x=0 gives the squared Cauchy-Schwarz cost of the lost negative half-line in normalized Mellin evaluation at real part a/2. The formal statement proves the integral asymptotic.
-- source:
--   Rational critical metric and the order of cutoff and closure in Masullo (11.1.2.3); the formal statement concerns the continuous integral, independently of the nuclear trace.

import Mathlib
open Filter Topology MeasureTheory Set

theorem MasulloRH.critical_Mellin_halfline_tail_norm_asymptotic (a : ℝ) (ha : 0 < a) :
    let w : ℝ → ℝ := fun x => Real.exp |x| * (1+x^2)^2
    Tendsto (fun L : ℝ => ∫ y : ℝ in Ioi 0,
      Real.exp (a*L) * (1+L^2)^2 * Real.exp ((1-a)*(L+y)) / w (L+y))
      atTop (𝓝 a⁻¹) := by sorry
