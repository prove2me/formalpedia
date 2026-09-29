-- Prove2me | Theorems.Thm_ModularCurve_laurent_qParam_coeff_unique
-- name    : ModularCurve.laurent_qParam_coeff_unique
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/e84024f0-c086-5b60-a768-d944a96ecf32
-- title:
--   Uniqueness of Laurent q-expansions at period h
-- statement:
--   Let $h$ be a real number with $h>0$, let $F\colon\mathfrak H\to\mathbb C$ be an arbitrary function on the upper half-plane, and let $A,B$ be formal Laurent series over $\mathbb C$ (elements of `LaurentSeries ℂ`, i.e. Hahn series over $\mathbb Z$ with complex coefficients). Assume that for every $\tau\in\mathfrak H$ the family $m\mapsto A_m\,q^m$, indexed by $m\in\mathbb Z$, is summable with sum $F(\tau)$, where $q=\mathrm{qParam}\,h\,\tau=e^{2\pi i\tau/h}$ and $q^m$ denotes the integer power of the nonzero complex number $q$; assume the same for the coefficients of $B$, again with sum $F(\tau)$ for every $\tau\in\mathfrak H$. The conclusion is that $A=B$ as formal Laurent series, that is, $A_m=B_m$ for all $m\in\mathbb Z$. Note that unconditional `HasSum` over the index set $\mathbb Z$ is required at every point of the upper half-plane; no holomorphy, growth or modularity hypothesis on $F$ is imposed.
--
--   This is the $q$-expansion principle in the form needed for Laurent (rather than Taylor) expansions: a function on $\mathfrak H$ determines at most one formal Laurent series realising it at a given period $h$. It is used throughout the treatment of modular functions and modular units on $X_0(N)$, for instance when identifying the Fricke involution on $q$-expansions and when comparing conjugates of modular polynomials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_laurent_qParam_coeff_unique.lean

import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.RingTheory.LaurentSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.laurent_qParam_coeff_unique (h : ℝ) (hh : 0 < h) (F : UpperHalfPlane → ℂ) (A B : LaurentSeries ℂ) (hA : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => A.coeff m * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ)) (hB : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => B.coeff m * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ)) : A = B := by sorry
