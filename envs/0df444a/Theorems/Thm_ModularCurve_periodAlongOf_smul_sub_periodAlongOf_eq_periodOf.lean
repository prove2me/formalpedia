-- Prove2me | Theorems.Thm_ModularCurve_periodAlongOf_smul_sub_periodAlongOf_eq_periodOf
-- name    : ModularCurve.periodAlongOf_smul_sub_periodAlongOf_eq_periodOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/d50e9f23-4238-5d81-8434-ac12f6471576
-- title:
--   Base-point independence of the period of γ
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$ of finite index, let $\gamma \in \Gamma$ and let $\tau$ be a point of the upper half-plane $\mathbb{H}$. For points $\tau_0,\tau_1 \in \mathbb{H}$, [`ModularCurve.periodAlongOf`](def/ModularCurve_PeriodOf.html#L42) $\Gamma\,\tau_0\,\tau_1$ denotes the $\mathbb{C}$-linear functional on the space of weight-two cusp forms $\mathrm{CuspForm}\,\Gamma\,2$ which sends $f$ to $\int_0^1 f(\mathrm{segmentPath}\,\tau_0\,\tau_1\,t)\,(\tau_1-\tau_0)\,dt$, the integral of $f(z)\,dz$ along the straight segment $t \mapsto \tau_0 + t(\tau_1-\tau_0)$ (with the parameter clamped to $[0,1]$), and [`ModularCurve.periodOf`](def/ModularCurve_PeriodOf.html#L56) $\Gamma\,\gamma$ is the functional $\mathrm{periodAlongOf}\,\Gamma\,i\,(\gamma \cdot i)$ attached to the segment from $i$ to $\gamma \cdot i$. The assertion is the equality of elements of $\mathrm{Hom}_{\mathbb{C}}(\mathrm{CuspForm}\,\Gamma\,2, \mathbb{C})$
--   $$\mathrm{periodAlongOf}\,\Gamma\,i\,(\gamma \cdot \tau) \; - \; \mathrm{periodAlongOf}\,\Gamma\,i\,\tau \; = \; \mathrm{periodOf}\,\Gamma\,\gamma,$$
--   where $\gamma$ acts on $\mathbb{H}$ through its image in $\mathrm{SL}_2(\mathbb{Z})$; that is, for every weight-two cusp form $f$ on $\Gamma$ the difference of the segment integrals from $i$ to $\gamma\tau$ and from $i$ to $\tau$ equals the integral from $i$ to $\gamma i$.
--
--   This is the base-point independence of the period homomorphism $\gamma \mapsto \int_i^{\gamma i} f(z)\,dz$ on weight-two cusp forms: moving a point of $\mathbb{H}$ within its $\Gamma$-orbit changes the Abel–Jacobi functional $\int_i^{\tau}$ by a period. It is used in the study of the period lattice of $\Gamma$ and in the statements about Abel–Jacobi images and fibre sums on the modular curve that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_periodAlongOf_smul_sub_periodAlongOf_eq_periodOf.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups

theorem ModularCurve.periodAlongOf_smul_sub_periodAlongOf_eq_periodOf
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (γ : Γ) (τ : UpperHalfPlane) :
    ModularCurve.periodAlongOf Γ UpperHalfPlane.I ((γ : SL(2, ℤ)) • τ) -
      ModularCurve.periodAlongOf Γ UpperHalfPlane.I τ = ModularCurve.periodOf Γ γ := by sorry
