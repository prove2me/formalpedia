-- Prove2me | Theorems.Thm_ModularCurve_periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf
-- name    : ModularCurve.periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/0113dc16-2a0e-5225-bf3e-ef9894c1eec1
-- title:
--   Segment period equals difference of primitive values
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb Z)$, let $f$ be a cusp form of weight $2$ for $\Gamma$, and let $F\colon\mathfrak H\to\mathbb C$ satisfy [`ModularCurve.HasEquivariantPrimitiveOf`](def/ModularCurve_PeriodOf.html#L71)$\,\Gamma\,f\,F$, that is: (i) for every $\tau\in\mathfrak H$ the function $F\circ\mathrm{ofComplex}$ has derivative $f(\tau)$ at the point $\tau$ of $\mathbb C$; (ii) $F$ tends to $0$ along the filter `atImInfty`; (iii) $F$ is an equivariant primitive in the sense that for each $\gamma\in\Gamma$ there is a constant $c\in\mathbb C$ with $F(\gamma\cdot z)-F(z)=c$ for all $z\in\mathfrak H$; and (iv) for every $\delta\in\mathrm{SL}_2(\mathbb Z)$ the function $w\mapsto F(\delta\cdot w)$ has a limit $L\in\mathbb C$ along `atImInfty`. Then for every $\gamma\in\Gamma$ the value at $f$ of the linear functional [`ModularCurve.periodOf`](def/ModularCurve_PeriodOf.html#L56)$\,\Gamma\,\gamma$ on $S_2(\Gamma)$ — by definition the integral $\int_0^1$ of the project's period integrand along the straight segment from $i$ to $\gamma\cdot i$, namely $t\mapsto f\bigl((1-t)i+t\,\gamma i\bigr)\,(\gamma i-i)$ — equals $F(\gamma\cdot i)-F(i)$.
--
--   This is the fundamental theorem of calculus along a segment in the upper half plane, identifying the two standard descriptions of the periods of a weight-$2$ cusp form: segment integrals, which define the period lattice inside $S_2(\Gamma)^\vee$, and differences of values of a primitive, which define the period map into group cohomology. It is used throughout the construction of the period lattice and the Abel–Jacobi dictionary for modular curves, and in the recognition of eigenforms by their $q$-coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf (Γ : Subgroup SL(2, ℤ))
    (f : CuspForm Γ 2) {F : UpperHalfPlane → ℂ}
    (hF : ModularCurve.HasEquivariantPrimitiveOf Γ f F) (γ : Γ) :
    ModularCurve.periodOf Γ γ f =
      F ((γ : SL(2, ℤ)) • UpperHalfPlane.I) - F UpperHalfPlane.I := by sorry
