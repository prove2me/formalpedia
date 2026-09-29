-- Prove2me | Theorems.Thm_ModularCurve_qParam_coeff_unique
-- name    : ModularCurve.qParam_coeff_unique
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/8190c564-9ec6-51fd-be96-ffe0839ea75f
-- title:
--   Uniqueness of q-expansion coefficients at period h
-- statement:
--   Let $h$ be a real number with $h>0$, let $F$ be an arbitrary function from the upper half-plane $\mathfrak H$ to $\mathbb C$ (no holomorphy or modularity is assumed), and let $c,d\colon\mathbb N\to\mathbb C$ be two sequences of complex numbers. Write $q_h(\tau)=\mathrm{Function.Periodic.qParam}\,h\,\tau=e^{2\pi i\tau/h}$ for the standard $q$-parameter of period $h$, evaluated at the complex number underlying $\tau$. Assume that for every $\tau\in\mathfrak H$ the family $m\mapsto c_m\,q_h(\tau)^m$, indexed by $m\in\mathbb N$, is summable with sum $F(\tau)$, and likewise that for every $\tau\in\mathfrak H$ the family $m\mapsto d_m\,q_h(\tau)^m$ is summable with sum $F(\tau)$; here summability is unconditional summability in $\mathbb C$ (Lean's `HasSum`), so in particular both series converge at every point of $\mathfrak H$ to the same value. The conclusion is the equality of the two sequences as functions $\mathbb N\to\mathbb C$, that is, $c_m=d_m$ for every $m\in\mathbb N$.
--
--   This is the uniqueness half of the $q$-expansion principle at period $h$, stated for bare functions on the upper half-plane and bare coefficient sequences: a function determines its $q$-expansion coefficients. It is used in the treatment of Siegel units, where coefficients of $q$-expansions of modular forms and of their slashes are identified and shown to be integral, and it is the input to the corresponding uniqueness statement for Laurent-type expansions in $q_h$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qParam_coeff_unique.lean

import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.qParam_coeff_unique (h : ℝ) (hh : 0 < h) (F : UpperHalfPlane → ℂ) (c d : ℕ → ℂ) (hc : ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ => c m * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ)) (hd : ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ => d m * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ)) : c = d := by sorry
