-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Geometry_prescribed_residual_regularity
-- name    : OAI.BalancedTransport.Geometry.prescribed_residual_regularity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:15:03.05503+00:00
-- url     : https://prove2.me/theorems/200b8c85-80ed-4830-b499-e2ea28ba6cd9
-- title:
--   A smooth periodic divergence-free velocity solves Navier–Stokes with its residual force
-- statement:
--   Let $K\subseteq\mathbb R^3$ be compact and let $U$ be a jointly smooth velocity that vanishes outside $K$, is $1$-periodic after time $1$, satisfies $U(0,\cdot)=0$, and is divergence free for $t\ge0$. Put
--   $$
--   f_0=\partial_tU+(U\cdot\nabla)U,\qquad f_1=-\Delta U,\qquad f=f_0+\nu f_1 .
--   $$
--   Then $f_0$ and $f_1$ are smooth on $t\ge0$, and $U,f_0,f_1$ vanish outside $K$ for $t\ge0$. Also $U,f_0,f_1$ have uniformly bounded mixed derivatives, and $U$ is $1$-periodic after time $1$. For every $\nu$, $U$ with zero pressure solves the Navier–Stokes equations $\partial_tU+(U\cdot\nabla)U=\nu\Delta U+f$ with $U(0)=0$. Moreover $f$ is smooth, has bounded mixed derivatives, and is $1$-periodic after time $1$.
--
--   This turns any admissible velocity into a forced Navier–Stokes solution, with force depending affinely on the viscosity.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/ResidualRegularity.lean#L132-L179

import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity

open OAI OAI.BalancedTransport OAI.BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem OAI.BalancedTransport.Geometry.prescribed_residual_regularity {K : Set Space} (hK : IsCompact K) {U : Velocity}
    (hU : JointSmooth U) (hs : SpatiallySupported K U) (hp : RepeatsAfter 1 U)
    (hzero : ∀ x, U 0 x = 0) (hdiv : ∀ t, 0 ≤ t → ∀ x, div U t x = 0) :
    Smooth (inertialCoefficient U) ∧ Smooth (viscousCoefficient U) ∧
    CommonCompactSupport U (inertialCoefficient U) (viscousCoefficient U) ∧
    BoundedMixed U ∧ BoundedMixed (inertialCoefficient U) ∧ BoundedMixed (viscousCoefficient U) ∧
    PeriodicAfterOne U ∧
    ∀ ν : ℝ, let f := affineForce (inertialCoefficient U) (viscousCoefficient U) ν
      ZeroDataSolution ν f U (fun _ _ => 0) ∧
      Smooth f ∧ BoundedMixed f ∧ PeriodicAfterOne f := by sorry
