-- Prove2me | Theorems.Thm_N25_analyticAt_and_integralQExp_invOfUnit
-- name    : N25.analyticAt_and_integralQExp_invOfUnit
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:27:12.508309+00:00
-- url     : https://prove2.me/theorems/3758ec79-272a-4a18-a839-01912b1515ec
-- title:
--   The reciprocal of a nowhere-zero integral q-expansion is analytic and integral
-- statement:
--   Let $f$ be a complex function and $p∈ℤ[[q]]$. Assume the cusp function of $f$ is analytic at $0$, $f$ is nowhere zero, $p(0)=1$, and $qexp(f)$ is the complex image of $p$. Then $$AnalyticAt_0(f^{-1})∧IntegralQExp(f^{-1},p^{-1}).$$ This closes the modular-unit construction under inversion.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitAnalytic

set_option autoImplicit false
open N25

theorem N25.analyticAt_and_integralQExp_invOfUnit
    (f : UpperHalfPlane → ℂ) (p : PowerSeries ℤ)
    (ha : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 f) 0)
    (hfn : ∀ τ : UpperHalfPlane, f τ ≠ 0)
    (hc : PowerSeries.constantCoeff p = 1)
    (hq : UpperHalfPlane.qExpansion 1 f = PowerSeries.map (Int.castRingHom ℂ) p) :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 (fun τ => (f τ)⁻¹)) 0 ∧
      ModularCurve.IsIntegralQExp (fun τ => (f τ)⁻¹) (p.invOfUnit (1 : ℤˣ)) := by sorry
