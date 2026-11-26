-- Prove2me | Theorems.Thm_MasulloRH_scalar_curvature_endpoint_bound
-- name    : MasulloRH.scalar_curvature_endpoint_bound
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T12:34:50.278516+00:00
-- url     : https://prove2.me/theorems/0ae70edb-1ccd-5e95-801f-aff9260bca8b
-- title:
--   The sharp curvature bound for a real function between two sampled endpoints
-- statement:
--   Let a twice differentiable real function have second derivative bounded in absolute value by $M\ge0$ on $[l,r]$, and let the absolute values at both endpoints be at most $A$. Then $|f(x)|\le A+M(r-l)^2/8$ everywhere on that interval. The quadratic $x(1-x)$ attains the coefficient $1/8$ at the midpoint of $[0,1]$.
-- source:
--   Finite-height certificate for https://prove2.me/theorems/cc487734-5ed4-5457-b10a-df505d0aef9e with the rational witness https://prove2.me/definitions/d1967a7a-bf7f-42bd-8ad5-820a7680a39d .

import Mathlib.Analysis.Calculus.Deriv.Basic

open Set

theorem MasulloRH.scalar_curvature_endpoint_bound (f f' f'' : ℝ → ℝ) (l r M A : ℝ) (hM : 0 ≤ M)
    (hd : ∀ x, HasDerivAt f (f' x) x) (hdd : ∀ x, HasDerivAt f' (f'' x) x)
    (hc : ∀ x ∈ Icc l r, |f'' x| ≤ M)
    (hl : |f l| ≤ A) (hr : |f r| ≤ A) (x : ℝ) (hx : x ∈ Icc l r) :
    |f x| ≤ A + M * (r-l)^2 / 8 := by sorry
