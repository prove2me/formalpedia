-- Prove2me | Theorems.Thm_OAI_Solenoidal_transitionReciprocal_bound
-- name    : OAI.Solenoidal.transitionReciprocal_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:44:30.70926+00:00
-- url     : https://prove2.me/theorems/590ff548-395a-4095-b247-867a07951f21
-- title:
--   The reciprocal of the smooth-step denominator $\psi(x)+\psi(1-x)$ is bounded by $16$
-- statement:
--   Let $\psi(x)=e^{-1/x}$ for $x>0$ and $\psi(x)=0$ for $x\le0$. The standard smooth step is $S(x)=\psi(x)/\big(\psi(x)+\psi(1-x)\big)$; its denominator is strictly positive for every real $x$, because at least one of $x$ and $1-x$ is positive. Let
--   $$\rho(x)=\frac{1}{\psi(x)+\psi(1-x)}$$
--   be the reciprocal of this denominator.
--
--   **Theorem.** For every $x\in\mathbb{R}$,
--
--   $$
--   |\rho(x)|\le16 .
--   $$
--
--   Since $S=\psi\cdot\rho$ and all derivatives of $\rho$ are polynomial expressions in $\rho$ and derivatives of $\psi$, this uniform bound is the basic estimate for explicit bounds on derivatives of smooth steps. Equivalently, the denominator satisfies $\psi(x)+\psi(1-x)\ge\frac1{16}$, which is used when approximating $\rho$ at rational points by interval arithmetic.
--
--   **Formalization Note** $\rho$ is `transitionReciprocal`, defined as `(expNegInvGlue x + expNegInvGlue (1-x))⁻¹`; the positivity of the denominator is Mathlib's `Real.smoothTransition.pos_denom`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/JetCalculus.lean#L75-L94

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

theorem OAI.Solenoidal.transitionReciprocal_bound (x : ℝ) : |transitionReciprocal x| ≤ 16 := by sorry
