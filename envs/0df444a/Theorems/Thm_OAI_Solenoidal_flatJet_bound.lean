-- Prove2me | Theorems.Thm_OAI_Solenoidal_flatJet_bound
-- name    : OAI.Solenoidal.flatJet_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:43:31.074243+00:00
-- url     : https://prove2.me/theorems/b395e46e-63ba-4541-8d26-420d6b508e68
-- title:
--   Uniform bound for a polynomial in $1/x$ times the flat function $e^{-1/x}$
-- statement:
--   Let $\psi:\mathbb{R}\to\mathbb{R}$ be the flat function $\psi(x)=e^{-1/x}$ for $x>0$ and $\psi(x)=0$ for $x\le0$. For a polynomial $p=\sum_n p_nX^n$ with rational coefficients define
--   $$F_p(x)=p(1/x)\,\psi(x)\quad(x>0),\qquad F_p(x)=0\quad(x\le0),\qquad \beta(p)=\sum_{n\ge0}|p_n|\,n!\in\mathbb{Q},$$
--   the sum being finite.
--
--   **Theorem.** For every $p\in\mathbb{Q}[X]$ and every $x\in\mathbb{R}$,
--
--   $$
--   \big|F_p(x)\big|\le\sum_{n\ge0}|p_n|\,n! .
--   $$
--
--   Every derivative of $\psi$ has the form $F_p$: the derivative of $F_p$ is $F_{X^2(p-p')}$. The theorem therefore gives explicit rational bounds, computable from the coefficients, for all derivatives of $\psi$ and of the smooth cut-off functions built from it, which is what is needed for effective bounds on derivatives of the constructed flows.
--
--   **Formalization Note** $F_p$ is `flatJet p`, defined as `(p.map (Rat.castHom ℝ)).eval x⁻¹ * expNegInvGlue x`, and $\beta(p)$ is `flatBound p`, summed over `p.support`. For $x\le0$ the factor `expNegInvGlue x` is $0$, so Lean's convention $0^{-1}=0$ plays no role.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/JetCalculus.lean#L44-L65

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

open OAI OAI.Solenoidal
open Set MeasureTheory Filter
open scoped BigOperators Topology Polynomial

theorem OAI.Solenoidal.flatJet_bound (p : ℚ[X]) (x : ℝ) : |flatJet p x| ≤ (flatBound p : ℝ) := by sorry
