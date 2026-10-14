-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_iteratedPartial_mul
-- name    : HunterPDE.Sobolev.iteratedPartial_mul
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T17:27:04.793301+00:00
-- url     : https://prove2.me/theorems/fb69dac0-771e-40f2-acc2-526cb3ab2a5e
-- title:
--   Higher product rule for smooth multi-index derivatives
-- statement:
--   For two globally smooth real functions u and v on Euclidean n-space, the beta derivative of their product at x is the sum over all coordinatewise sub-indices gamma of beta of the multi-index binomial coefficient times the beta-minus-gamma derivative of u and the gamma derivative of v. The finite sum is over the canonical lower interval of beta. There is no initial derivative shift and no weak derivative or measure hypothesis. The result follows by iterating the ordinary coordinate product rule.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, section 1.8 printed p. 10 and Proposition 3.16 proof printed p. 54. Derived classical multi-index calculus identity.

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Pi.Interval

open HunterPDE.Sobolev
set_option autoImplicit false

theorem HunterPDE.Sobolev.iteratedPartial_mul {n : ℕ}
    (u v : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v)
    (β : Fin n → ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    iteratedPartial β (fun y => u y * v y) x =
      ∑ γ ∈ Finset.Iic β, (∏ i, (Nat.choose (β i) (γ i) : ℝ)) *
        (iteratedPartial (fun i => β i - γ i) u x * iteratedPartial γ v x) := by sorry
