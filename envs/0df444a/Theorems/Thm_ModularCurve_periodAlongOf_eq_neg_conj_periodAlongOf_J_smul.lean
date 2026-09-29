-- Prove2me | Theorems.Thm_ModularCurve_periodAlongOf_eq_neg_conj_periodAlongOf_J_smul
-- name    : ModularCurve.periodAlongOf_eq_neg_conj_periodAlongOf_J_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/51e06212-7adc-5847-91d8-f78bfe608a12
-- title:
--   Segment periods under the anti-holomorphic involution τ↦-τ̄
-- statement:
--   Let $\Gamma$ be an arbitrary subgroup of $\mathrm{SL}_2(\mathbb{Z})$ and let $f,g$ be cusp forms of weight $2$ for $\Gamma$. Write $J$ for the element of $\mathrm{GL}_2(\mathbb{R})$ acting on the upper half-plane $\mathfrak{H}$ by the anti-holomorphic involution $\tau\mapsto-\bar\tau$, and assume that $g(\tau)=\overline{f(J\cdot\tau)}$ for every $\tau\in\mathfrak{H}$. For $\tau_0,\tau_1\in\mathfrak{H}$, [`ModularCurve.periodAlongOf`](def/ModularCurve_PeriodOf.html#L42) $\Gamma\,\tau_0\,\tau_1$ denotes the $\mathbb{C}$-linear functional on weight-two cusp forms for $\Gamma$ given by the integral along the straight segment from $\tau_0$ to $\tau_1$ in its affine parametrisation, namely $h\mapsto\int_0^1 h\bigl((1-t)\tau_0+t\tau_1\bigr)(\tau_1-\tau_0)\,dt$ (here the integrand is `periodIntegrandOf` and the segment point is `segmentPath`). The assertion is that for all $\tau_0,\tau_1\in\mathfrak{H}$,
--   $$\int_{\tau_0}^{\tau_1} g = -\overline{\int_{J\cdot\tau_0}^{J\cdot\tau_1} f},$$
--   that is, the period of $g$ along the segment from $\tau_0$ to $\tau_1$ equals minus the complex conjugate of the period of $f$ along the segment from $-\bar\tau_0$ to $-\bar\tau_1$.
--
--   This is the compatibility of weight-two segment period integrals with the anti-holomorphic involution $\tau\mapsto-\bar\tau$ of $\mathfrak{H}$, the analytic input for the real structure on period lattices and for complex conjugation acting on modular symbols. It is used in the constructions of the Eichler–Shimura isomorphism for $H^1$ of $\Gamma_H$-curves and in the statements identifying $\mathrm{Pic}^0$ of the complex modular curve $X_H$ with a quotient by the period lattice, Hecke-equivariantly.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_periodAlongOf_eq_neg_conj_periodAlongOf_J_smul.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.periodAlongOf_eq_neg_conj_periodAlongOf_J_smul
    (Γ : Subgroup SL(2, ℤ)) (f g : CuspForm Γ 2)
    (hg : ∀ τ : UpperHalfPlane, g τ = (starRingEnd ℂ) (f (UpperHalfPlane.J • τ)))
    (τ₀ τ₁ : UpperHalfPlane) :
    ModularCurve.periodAlongOf Γ τ₀ τ₁ g =
      -(starRingEnd ℂ) (ModularCurve.periodAlongOf Γ (UpperHalfPlane.J • τ₀) (UpperHalfPlane.J • τ₁) f) := by sorry
