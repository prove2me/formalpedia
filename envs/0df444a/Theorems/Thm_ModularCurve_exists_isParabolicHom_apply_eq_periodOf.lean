-- Prove2me | Theorems.Thm_ModularCurve_exists_isParabolicHom_apply_eq_periodOf
-- name    : ModularCurve.exists_isParabolicHom_apply_eq_periodOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/8e18b553-ffc9-596d-bb1b-02d2550dd2fb
-- title:
--   Periods as a parabolic homomorphism Γ → S₂(Γ)^∨
-- statement:
--   Let $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$ be a subgroup of finite index (the finite-index hypothesis being a typeclass assumption). The assertion is the existence of a homomorphism of additive groups $\Phi$ from `Additive Γ`, the group $\Gamma$ written additively, to the $\mathbb{C}$-linear dual `Module.Dual ℂ (CuspForm Γ 2)` of the space of weight-$2$ cusp forms for $\Gamma$, with two properties. First, $\Phi$ satisfies [`ModularCurve.Period.IsParabolicHom`](def/ModularCurve_PeriodMap.html#L15), that is, $\Phi(\gamma) = 0$ for every $\gamma \in \Gamma$ whose underlying integer $2 \times 2$ matrix has $\operatorname{tr}(\gamma)^2 = 4$; note that this condition is imposed on the square of the trace, so it covers $\pm I$ as well as the genuinely parabolic elements. Second, $\Phi$ takes the prescribed values: for every $\gamma \in \Gamma$, the functional $\Phi(\gamma)$ equals [`ModularCurve.periodOf Γ γ`](def/ModularCurve_PeriodOf.html#L56), which by definition is `periodAlongOf Γ` applied to the pair of points $i$ and $\gamma \cdot i$ of the upper half-plane, namely the functional sending a cusp form $f$ to $\int_0^1 \mathtt{periodIntegrandOf}\,\Gamma\, i\, (\gamma \cdot i)\, f\, t \, dt$, the integral over the unit parameter interval of the integrand attached to the path from $i$ to $\gamma \cdot i$. In particular the map $\gamma \mapsto$ `periodOf Γ γ` is itself additive in $\gamma$ and vanishes on elements of trace square $4$.
--
--   This is the Eichler–Shimura period character of $S_2(\Gamma)$: the periods $f \mapsto \int_i^{\gamma i} f(\tau)\,d\tau$ form a parabolic $1$-cocycle on $\Gamma$ with values in $S_2(\Gamma)^\vee$, here in the form of an honest additive homomorphism on $\Gamma$ vanishing on elements with $\operatorname{tr}^2 = 4$. It is used downstream in [`ModularCurve.exists_cuspForm_multiplier_eq_exp_periodOf_of_norm_eq_one`](thm.html#ModularCurve.exists_cuspForm_multiplier_eq_exp_periodOf_of_norm_eq_one) and in [`ModularCurve.petersson_mem_periodLatticeOf_iff_re_periodOf_int`](thm.html#ModularCurve.petersson_mem_periodLatticeOf_iff_re_periodOf_int).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_isParabolicHom_apply_eq_periodOf.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Topology ComplexConjugate

theorem ModularCurve.exists_isParabolicHom_apply_eq_periodOf (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    ∃ Φ : Additive Γ →+ Module.Dual ℂ (CuspForm Γ 2),
      ModularCurve.Period.IsParabolicHom Γ Φ ∧
        ∀ γ : Γ, Φ (Additive.ofMul γ) = ModularCurve.periodOf Γ γ := by sorry
