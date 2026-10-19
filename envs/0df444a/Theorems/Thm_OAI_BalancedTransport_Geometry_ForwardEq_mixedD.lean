-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Geometry_ForwardEq_mixedD
-- name    : OAI.BalancedTransport.Geometry.ForwardEq.mixedD
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:14:28.018204+00:00
-- url     : https://prove2.me/theorems/858dd0bf-6205-413d-ab33-516e0849a2d4
-- title:
--   Fields that agree for nonnegative times have the same mixed derivatives there
-- statement:
--   A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, with values in a normed space. It is jointly smooth when $(t,x)\mapsto v(t,x)$ is $C^\infty$. A multi-index is a list whose entries are either time or a spatial direction. The mixed derivative $\partial^av$ applies the corresponding derivatives in order, where the time derivative used on the solution side is the one-sided derivative within $[0,\infty)$; the full mixed derivative uses the ordinary time derivative instead. If $v(t,\cdot)=w(t,\cdot)$ for every $t\ge0$, then for every multi-index $a$,
--   $$
--   \partial^av(t,\cdot)=\partial^aw(t,\cdot)\qquad(t\ge0).
--   $$
--
--   So the construction may modify fields at negative times without affecting any statement about $t\ge0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/ResidualRegularity.lean#L15-L30

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

theorem OAI.BalancedTransport.Geometry.ForwardEq.mixedD {v w : Field F} (h : ForwardEq v w) (a : MultiIndex) :
    ForwardEq (BalancedTransport.mixedD a v) (BalancedTransport.mixedD a w) := by sorry
