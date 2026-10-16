-- Prove2me | Theorems.Thm_OAI_Solenoidal_tensorVelocity_formula
-- name    : OAI.Solenoidal.tensorVelocity_formula
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:46:11.479621+00:00
-- url     : https://prove2.me/theorems/d9a4fe4e-f921-4dcd-934c-83d7927b121e
-- title:
--   Tensor-product velocity fields with periodic-jet profiles admit explicit symbolic formulas on the period cell
-- statement:
--   Let $\psi(x)=e^{-1/x}$ for $x>0$ and $\psi(x)=0$ for $x\le0$. A *jet expression* is a finite expression in one real variable built from rational constants, the variable $x$, sums, products, rational affine substitutions $E\mapsto E(ax+b)$ with $a,b\in\mathbb{Q}$, the flat functions $x\mapsto p(1/x)\,\psi(x)$ with $p\in\mathbb{Q}[X]$, and the function $\rho(x)=1/\big(\psi(x)+\psi(1-x)\big)$; each expression $E$ evaluates to a function $[\![E]\!]:\mathbb{R}\to\mathbb{R}$. A *periodic jet* of period $T\in\mathbb{Q}$, $T>0$, for a function $g:\mathbb{R}\to\mathbb{R}$ consists of the facts that $g$ is $C^\infty$ and $T$-periodic together with a jet expression $E$ such that $g=[\![E]\!]$ on $[0,T]$.
--
--   A *box expression* is a finite expression on space-time $z=(t,x_0,x_1,x_2)$ built from rational constants, terms $E(z_k)$ obtained by evaluating a jet expression $E$ at one coordinate $z_k$ of $z$, sums and products. A field $u:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}^3$ *has a rational formula* if there are box expressions $F_0,F_1,F_2$ such that
--   $$u(t,x)=\big([\![F_0]\!](t,x),\,[\![F_1]\!](t,x),\,[\![F_2]\!](t,x)\big)\qquad\text{for all }(t,x)\in[0,1]\times[0,10]^3 .$$
--   For $i\in\{0,1,2\}$ and $g_0,g_1,g_2:\mathbb{R}\to\mathbb{R}$, the tensor velocity is the time-independent field $U_{i,g}(t,x)=g_0(x_0)\,g_1(x_1)\,g_2(x_2)\,e_i$.
--
--   **Theorem.** If each of $g_0,g_1,g_2$ admits a periodic jet of period $10$, then $U_{i,g}$ has a rational formula:
--
--   $$
--   \exists\,F_0,F_1,F_2:\quad U_{i,g}(t,x)=\big([\![F_k]\!](t,x)\big)_{k=0,1,2}\quad\text{for all }(t,x)\in[0,1]\times[0,10]^3 .
--   $$
--
--   The pulses that drive the flows are tensor products of periodized one-dimensional profiles. This result turns one-dimensional symbolic descriptions of the profiles into a finite symbolic description of the whole three-dimensional field on the period cell, the first step towards algorithms that evaluate the field and its derivatives.
--
--   **Formalization Note** Jet expressions are the inductive type `JetExpr`, periodic jets are the structure `PeriodicJet 10 (g j)` (its existence is assumed via `Nonempty`), box expressions are `BoxExpr`, and the conclusion is `HasRationalFormula (tensorVelocity i g)`, whose period cell is `closedPeriodCell`. The formula is obtained by choice and is not claimed to be computed from the hypotheses.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/RationalFormula.lean#L125-L146

import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Differential
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ScheduledForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ClassicalRegularity
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_EnergyIdentities
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RectangleGeometry
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Trajectories
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Pulses
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Localization
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ShearCore
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Routing
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_JetCalculus
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_JetProfiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_BoxJets
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RationalFormula

open OAI OAI.Solenoidal
open Set MeasureTheory Filter
open scoped BigOperators Topology

theorem OAI.Solenoidal.tensorVelocity_formula (i : Fin 3) (g : Fin 3 → ℝ → ℝ)
    (h : ∀ j, Nonempty (PeriodicJet 10 (g j))) :
    HasRationalFormula (tensorVelocity i g) := by sorry
