-- Prove2me | Theorems.Thm_OAI_Solenoidal_globalDirectForce_classicalSolution
-- name    : OAI.Solenoidal.globalDirectForce_classicalSolution
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:33:18.258995+00:00
-- url     : https://prove2.me/theorems/aaa3a26f-0c4f-4f0d-ab3f-d27e6c8402d8
-- title:
--   A smooth periodic divergence-free field without self-advection solves forced Navier–Stokes with zero pressure
-- statement:
--   Let $u:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}^3$ be a time-dependent vector field and $\nu\in\mathbb{R}$. Write $\partial_j$ ($j=0,1,2$) for spatial partial derivatives, $\Delta u=\sum_j\partial_j\partial_ju$ for the spatial Laplacian, $\operatorname{div}u=\sum_j\partial_ju_j$, and $(u\cdot\nabla)u(t,x)=D_xu(t,x)[u(t,x)]$ for the advection term. Assume:
--
--   1. $(t,x)\mapsto u(t,x)$ is $C^\infty$ on $\mathbb{R}\times\mathbb{R}^3$;
--   2. $u(t,x+10k)=u(t,x)$ for all $t\in\mathbb{R}$, $x\in\mathbb{R}^3$, $k\in\mathbb{Z}^3$;
--   3. $\operatorname{div}u(t,x)=0$ for all $t\in\mathbb{R}$, $x\in\mathbb{R}^3$;
--   4. $u(0,x)=0$ for all $x\in\mathbb{R}^3$;
--   5. $(u\cdot\nabla)u(t,x)=0$ for all $t\in\mathbb{R}$, $x\in\mathbb{R}^3$.
--
--   Define the forcing
--   $$f(t,x)=\frac{\partial u}{\partial t}(t,x)-\nu\,\Delta u(t,x),$$
--   using the ordinary two-sided time derivative.
--
--   Recall that a triple $(f,u,p)$ with pressure $p:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}$ is a *classical solution* with viscosity $\nu$ if: $u$ and $p$ are $10\mathbb{Z}^3$-periodic in space; for every $T\ge0$, $u$, $\partial_tu$, $\partial_ju$, $\partial_j\partial_iu$, $p$ and $\nabla p$ are continuous on $[0,T]\times\mathbb{R}^3$, where $\partial_tu$ denotes the one-sided time derivative within $[0,\infty)$; for every $t\ge0$, $s\mapsto u(s,x)$ is differentiable within $[0,\infty)$ at $t$, and $u(t,\cdot)$, $\partial_ju(t,\cdot)$, $p(t,\cdot)$ are differentiable; for $t\ge0$, $\int_{[0,10)^3}p(t,x)\,dx=0$ and $\operatorname{div}u(t,\cdot)=0$; $u(0,\cdot)=0$; and for all $t\ge0$, $x\in\mathbb{R}^3$,
--   $$\partial_tu+(u\cdot\nabla)u=-\nabla p+\nu\,\Delta u+f .$$
--
--   **Theorem.** Under assumptions 1 to 5, $(f,u,0)$ is a classical solution with viscosity $\nu$, for the forcing $f=\partial_tu-\nu\,\Delta u$ defined above and pressure $p\equiv0$.
--
--   This is the direct-forcing principle behind the construction: a smooth, periodic, incompressible flow whose self-advection vanishes (for instance a shear flow switched on and off in time) is an exact Navier–Stokes solution without pressure, driven by the forcing obtained by solving the momentum equation for $f$. Properties of the forcing, such as smoothness, periodicity and effectivity, can then be read off from $u$.
--
--   **Formalization Note** The forcing is `globalDirectForce ν u t x = fullTimePartial u t x - ν • laplacian u t x`, where `fullTimePartial` uses the two-sided `deriv`, whereas `ClassicalSolution` uses `timePartial`, a `derivWithin` on `Set.Ici 0`. `Smooth u` is `ContDiff ℝ ⊤` of the uncurried map with `⊤ : ℕ∞`, i.e. $C^\infty$. Spatial derivatives are Fréchet derivatives (`fderiv`).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/Differential.lean#L267-L299

import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Differential

open OAI OAI.Solenoidal
open Set MeasureTheory
open scoped BigOperators
open Filter
open scoped Topology

theorem OAI.Solenoidal.globalDirectForce_classicalSolution {u : Field} (hu : Smooth u)
    (hp : SpatiallyPeriodic u) (hdiv : DivergenceFree u)
    (hzero : ∀ x, u 0 x = 0) (hadv : ∀ t x, advection u t x = 0) (ν : ℝ) :
    ClassicalSolution ν (globalDirectForce ν u) u (0 : Pressure) := by sorry
