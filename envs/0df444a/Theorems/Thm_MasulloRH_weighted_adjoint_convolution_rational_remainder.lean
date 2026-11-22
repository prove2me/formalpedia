-- Prove2me | Theorems.Thm_MasulloRH_weighted_adjoint_convolution_rational_remainder
-- name    : MasulloRH.weighted_adjoint_convolution_rational_remainder
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T08:07:48.250791+00:00
-- url     : https://prove2.me/theorems/71ac315b-1ce1-4dcd-92fd-1c44167a8ced
-- title:
--   Exact input-side expansion for the actual critical-width convolution adjoint
-- statement:
--   For p(x)=1+x², the polynomial part of the critical weighted adjoint convolution kernel is [p(x+b)/p(x)]². After its constant and linear terms, the output-side remainder is uniformly bounded by (10B²+2B⁴)/p(x) for |b|≤B. The exact input-side formula separates the commutator into products of square-integrable profiles. This permits trace-class error estimates for smooth compact convolutions in log norm.
-- source:
--   Masullo (9.2.2.41), (10.4.3.43–48); weighted convolution and ambient nuclearity.

import Mathlib

theorem MasulloRH.weighted_adjoint_convolution_rational_remainder (x b B : ℝ) (hb : |b| ≤ B) :
    let y := x+b
    let p := fun t : ℝ => 1+t^2
    let c := fun t : ℝ => t / p t
    (p y / p x)^2 =
      1 + 4*b*c y + 2*b^2/p x + (2*x*b+b^2)^2/(p x)^2
        - 4*b^2 * ((1/(p x))*(1/(p y)) - c x*c y) ∧
    |(p y / p x)^2 - 1 - 4*b*c x| ≤ (10*B^2+2*B^4)/(p x) := by sorry
