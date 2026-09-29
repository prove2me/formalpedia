-- Prove2me | Theorems.Thm_ModularCurve_exists_hasEquivariantPrimitiveOf
-- name    : ModularCurve.exists_hasEquivariantPrimitiveOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/b21b1f0a-8a14-5943-be94-173ff5197938
-- title:
--   Existence of an admissible equivariant primitive of a weight-2 cusp form
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb Z)$ of finite index and let $f$ be a cusp form of weight $2$ for $\Gamma$. Then there exists a function $F\colon \mathfrak H \to \mathbb C$ on the upper half-plane satisfying the four conditions packaged by [`ModularCurve.HasEquivariantPrimitiveOf`](def/ModularCurve_PeriodOf.html#L71): (i) for every $\tau \in \mathfrak H$ the composite of $F$ with the retraction `ofComplex` of $\mathbb C$ onto $\mathfrak H$ is complex-differentiable at the point $\tau \in \mathbb C$ with derivative $f(\tau)$, so that $F$ is a holomorphic primitive of $f$; (ii) $F$ tends to $0$ along the filter `atImInfty`, i.e. $F(\tau) \to 0$ as $\operatorname{Im}\tau \to \infty$; (iii) $F$ is an equivariant primitive for $\Gamma$ in the sense that for each $\gamma \in \Gamma$ there is a constant $c \in \mathbb C$ with $F(\gamma \cdot z) - F(z) = c$ for all $z \in \mathfrak H$; and (iv) for every $\delta \in \mathrm{SL}_2(\mathbb Z)$ the function $w \mapsto F(\delta \cdot w)$ has a limit $L \in \mathbb C$ along `atImInfty`, i.e. $F$ has a finite limiting value at every cusp.
--
--   This is the existence statement underlying the Eichler–Shimura period integral of a weight-2 cusp form: the primitive $\int^\tau f$, normalised to vanish at $i\infty$, whose coboundary on $\Gamma$ is the period homomorphism and which stays bounded at every cusp. It is the input to the construction of the period map and period lattice on modular curves, and is used in the Abel–Jacobi and Hecke-eigenform arguments that rest on them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_hasEquivariantPrimitiveOf.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_hasEquivariantPrimitiveOf (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (f : CuspForm Γ 2) :
    ∃ F : UpperHalfPlane → ℂ, ModularCurve.HasEquivariantPrimitiveOf Γ f F := by sorry
