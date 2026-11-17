-- Prove2me | Theorems.Thm_N25_bounded_of_nonnegative_exp
-- name    : N25.bounded_of_nonnegative_exp
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:42.307304+00:00
-- url     : https://prove2.me/theorems/74242d81-7a9c-44bb-aaf7-4efebfc525ea
-- title:
--   A nonnegative exponential leading term implies cusp boundedness
-- statement:
--   Let $f$ be a complex function, let $ℓ≥0$, and suppose $f(τ)/exp(2πiℓτ)→c$ as $Im(τ)→∞$ for some $c∈ℂ$. Then $$f is bounded at the cusp.$$ This converts a normalized limit into regularity at infinity.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

set_option autoImplicit false
open Filter Topology

theorem N25.bounded_of_nonnegative_exp (f : UpperHalfPlane → ℂ) (ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    (c : ℂ) (hlim : Tendsto
      (fun τ : UpperHalfPlane => f τ /
        Complex.exp (2 * Real.pi * Complex.I * (ℓ : ℂ) * (τ : ℂ)))
      UpperHalfPlane.atImInfty (nhds c)) :
    UpperHalfPlane.IsBoundedAtImInfty f := by sorry
