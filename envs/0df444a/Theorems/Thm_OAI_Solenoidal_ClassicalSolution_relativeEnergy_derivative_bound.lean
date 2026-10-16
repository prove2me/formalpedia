-- Prove2me | Theorems.Thm_OAI_Solenoidal_ClassicalSolution_relativeEnergy_derivative_bound
-- name    : OAI.Solenoidal.ClassicalSolution.relativeEnergy_derivative_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:37:11.337656+00:00
-- url     : https://prove2.me/theorems/42df623e-2133-408f-89f8-bf68f7cc9f59
-- title:
--   Relative energy inequality for two classical periodic Navier–Stokes solutions with the same forcing
-- statement:
--   Throughout, points of $\mathbb{R}^3$ are written $x=(x_0,x_1,x_2)$, $e_0,e_1,e_2$ is the standard basis, $a\cdot b$ is the Euclidean dot product and $|a|^2=a\cdot a$. Let $Q=[0,10)^3$ be the fundamental cell of the lattice $10\mathbb{Z}^3$. For a velocity field $u:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}^3$ write $\partial_j u(t,x)=D_x u(t,x)[e_j]$ for the spatial partial derivatives, $\Delta u=\sum_j\partial_j\partial_j u$, $(u\cdot\nabla)u(t,x)=D_x u(t,x)[u(t,x)]$, $\operatorname{div}u=\sum_j\partial_j u_j$, and $\partial_t u(t,x)$ for the derivative of $s\mapsto u(s,x)$ within the half-line $[0,\infty)$ (one-sided at $t=0$).
--
--   Given $\nu\in\mathbb{R}$ and a forcing field $f:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}^3$, a pair $(u,p)$ with a pressure $p:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}$ is a *classical solution* with viscosity $\nu$ and forcing $f$ if:
--
--   1. $u(t,\cdot)$ and $p(t,\cdot)$ are $10\mathbb{Z}^3$-periodic for every $t$;
--   2. on every slab $[0,T]\times\mathbb{R}^3$ with $T\ge0$ the functions $u$, $\partial_t u$, $\partial_j u$, $\partial_j\partial_i u$, $p$ and $\nabla p$ are continuous, and for every $t\ge0$ the maps $u(t,\cdot)$, $\partial_j u(t,\cdot)$ and $p(t,\cdot)$ are differentiable and $s\mapsto u(s,x)$ is differentiable within $[0,\infty)$ at $t$;
--   3. for $t\ge0$: $\int_Q p(t,x)\,dx=0$ and $\operatorname{div}u(t,\cdot)=0$; moreover $u(0,\cdot)=0$;
--   4. for all $t\ge0$ and $x\in\mathbb{R}^3$: $\partial_t u+(u\cdot\nabla)u=-\nabla p+\nu\,\Delta u+f$.
--
--   **Theorem.** Let $(u,r)$ and $(v,p)$ be classical solutions with the same viscosity $\nu$ and the same forcing $f$, and assume $\nu\ge0$. Let $t\ge0$ and $B\ge0$ be such that $\max_k|\partial_j u_k(t,x)|\le B$ for all $x\in Q$ and $j\in\{0,1,2\}$. Then
--
--   $$
--   \int_Q \big(v(t,x)-u(t,x)\big)\cdot\big(\partial_t v(t,x)-\partial_t u(t,x)\big)\,dx\;\le\;6B\,E(t),\qquad E(t)=\int_Q\tfrac12\,|v(t,x)-u(t,x)|^2\,dx .
--   $$
--
--   The left-hand side is the time derivative of the relative energy $E$, so the theorem is the differential inequality $E'\le 6BE$ that drives a Grönwall argument: both solutions start from rest, so $E(0)=0$, and a bound on the spatial gradient of $u$ then forces $E\equiv0$. This is the mechanism behind uniqueness of classical solutions for a given forcing; nothing is assumed about $v$ beyond being a classical solution, and the two pressures may differ.
--
--   **Formalization Note** The bound on $\partial_j u$ is stated with Lean's default norm on `Fin 3 → ℝ`, the maximum of the absolute values of the components. `ClassicalSolution ν f u p` bundles conditions 1–4, the time derivative is `derivWithin` on `Set.Ici 0`, and $E(t)$ is `relativeEnergy u v t`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/EnergyIdentities.lean#L294-L353

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

theorem OAI.Solenoidal.ClassicalSolution.relativeEnergy_derivative_bound
    {ν : ℝ} {f u v : Field} {p r : Pressure}
    (hu : ClassicalSolution ν f u r) (hv : ClassicalSolution ν f v p)
    (hν : 0 ≤ ν) {t B : ℝ} (ht : 0 ≤ t) (hB : 0 ≤ B)
    (hgrad : ∀ x ∈ fundamentalCell, ∀ j, ‖spatialPartial u j t x‖ ≤ B) :
    (∫ x in fundamentalCell, euclidDot (v t x-u t x)
      (timePartial v t x-timePartial u t x)) ≤ (6*B) * relativeEnergy u v t := by sorry
