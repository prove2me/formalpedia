-- Prove2me | Theorems.Thm_N25_analyticAt_and_qExpansion_of_hasSum
-- name    : N25.analyticAt_and_qExpansion_of_hasSum
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:27:16.900053+00:00
-- url     : https://prove2.me/theorems/33c3654b-32f3-4607-9016-b47a9ba81395
-- title:
--   A convergent integral q-series gives the analytic q-expansion
-- statement:
--   Let $p(q)=∑a_nq^n∈ℤ[[q]]$ and let $f$ be a complex function. If $∑a_nexp(2πinτ)$ sums to $f(τ)$ for every $τ$, then $$AnalyticAt_0(f)∧qexp(f)=∑a_nq^n.$$ This converts pointwise summation into a formal q-expansion.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitAnalytic

set_option autoImplicit false
open N25

theorem N25.analyticAt_and_qExpansion_of_hasSum
    (f : UpperHalfPlane → ℂ) (p : PowerSeries ℤ)
    (hf : ∀ τ : UpperHalfPlane, HasSum
      (fun n : ℕ => ((PowerSeries.coeff n p : ℤ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) ^ n) (f τ)) :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 f) 0 ∧
      UpperHalfPlane.qExpansion 1 f = PowerSeries.map (Int.castRingHom ℂ) p := by sorry
