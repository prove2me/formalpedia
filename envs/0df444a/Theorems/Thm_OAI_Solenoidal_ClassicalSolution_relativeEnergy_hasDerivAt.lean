-- Prove2me | Theorems.Thm_OAI_Solenoidal_ClassicalSolution_relativeEnergy_hasDerivAt
-- name    : OAI.Solenoidal.ClassicalSolution.relativeEnergy_hasDerivAt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:36:35.58599+00:00
-- url     : https://prove2.me/theorems/f5a5ae7a-cef5-4445-88d9-5b8fdff6a606
-- title:
--   Time derivative of the relative kinetic energy of two classical Navier–Stokes solutions
-- statement:
--   Let $\nu\in\mathbb{R}$ and let $f:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}^3$ be a forcing field. For a velocity $w:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}^3$ write $\partial_tw$ for the one-sided time derivative of $s\mapsto w(s,x)$ within $[0,\infty)$, $\partial_j$ ($j=0,1,2$) for spatial partial derivatives, $\operatorname{div}w=\sum_j\partial_jw_j$, $\Delta w=\sum_j\partial_j\partial_jw$ and $(w\cdot\nabla)w(t,x)=D_xw(t,x)[w(t,x)]$. A pair $(w,\pi)$ of a velocity and a pressure $\pi:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}$ is a *classical solution* for $(\nu,f)$ if: $w$ and $\pi$ are $10\mathbb{Z}^3$-periodic in space; for every $T\ge0$, $w$, $\partial_tw$, $\partial_jw$, $\partial_j\partial_iw$, $\pi$ and $\nabla\pi$ are continuous on $[0,T]\times\mathbb{R}^3$; for $t\ge0$, $s\mapsto w(s,x)$ is differentiable within $[0,\infty)$ at $t$, and $w(t,\cdot)$, $\partial_jw(t,\cdot)$, $\pi(t,\cdot)$ are differentiable; for $t\ge0$, $\int_{[0,10)^3}\pi(t,x)\,dx=0$ and $\operatorname{div}w(t,\cdot)=0$; $w(0,\cdot)=0$; and $\partial_tw+(w\cdot\nabla)w=-\nabla\pi+\nu\,\Delta w+f$ for all $t\ge0$, $x\in\mathbb{R}^3$.
--
--   For two velocities $u,v$ define the relative kinetic energy
--   $$\mathcal E(s)=\int_{[0,10)^3}\tfrac12\,\bigl|v(s,x)-u(s,x)\bigr|^2\,dx\qquad(s\in\mathbb{R}),$$
--   where $|\cdot|$ is the Euclidean norm on $\mathbb{R}^3$.
--
--   **Theorem.** Let $(u,r)$ and $(v,p)$ be classical solutions for the same $(\nu,f)$, and let $t>0$. Then $\mathcal E$ is differentiable at $t$, with
--   $$\mathcal E'(t)=\int_{[0,10)^3}\bigl(v(t,x)-u(t,x)\bigr)\cdot\bigl(\partial_tv(t,x)-\partial_tu(t,x)\bigr)\,dx,$$
--   where $\cdot$ is the Euclidean inner product on $\mathbb{R}^3$ (for $t>0$ the one-sided time derivatives are ordinary derivatives).
--
--   This is the first step of the energy method for uniqueness of classical solutions: inserting the two momentum equations into the right-hand side, the pressure and transport contributions integrate to zero over the period cell and, for $\nu\ge0$, the viscous contribution is nonpositive, which leads to a differential inequality forcing $\mathcal E\equiv0$ on $[0,\infty)$.
--
--   **Formalization Note** In Lean, `relativeEnergy u v t = ∫ x in fundamentalCell, kineticDensity (v t x - u t x)` with `kineticDensity a = ∑ i, a i * a i / 2`, and the inner product is `euclidDot a b = ∑ i, a i * b i`. The conclusion is a two-sided `HasDerivAt` at $t>0$, and `timePartial` is `derivWithin` on `Set.Ici 0`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/EnergyIdentities.lean#L265-L280

import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Differential
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ScheduledForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ClassicalRegularity
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_EnergyIdentities

open OAI OAI.Solenoidal
open Set MeasureTheory
open scoped BigOperators
open Set MeasureTheory Filter
open scoped BigOperators Topology

theorem OAI.Solenoidal.ClassicalSolution.relativeEnergy_hasDerivAt {ν : ℝ} {f u v : Field} {p r : Pressure}
    (hu : ClassicalSolution ν f u r) (hv : ClassicalSolution ν f v p) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (relativeEnergy u v)
      (∫ x in fundamentalCell, euclidDot (v t x-u t x) (timePartial v t x-timePartial u t x)) t := by sorry
