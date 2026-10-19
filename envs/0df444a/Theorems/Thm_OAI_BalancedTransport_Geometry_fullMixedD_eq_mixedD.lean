-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Geometry_fullMixedD_eq_mixedD
-- name    : OAI.BalancedTransport.Geometry.fullMixedD_eq_mixedD
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:11:19.639873+00:00
-- url     : https://prove2.me/theorems/d92cd180-4a33-40b5-99b0-65fd8e0d5486
-- title:
--   One-sided and full mixed derivatives agree at nonnegative times
-- statement:
--   A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, with values in a normed space. It is jointly smooth when $(t,x)\mapsto v(t,x)$ is $C^\infty$. A multi-index is a list whose entries are either time or a spatial direction. The mixed derivative $\partial^av$ applies the corresponding derivatives in order, where the time derivative used on the solution side is the one-sided derivative within $[0,\infty)$; the full mixed derivative uses the ordinary time derivative instead. If $v$ is jointly smooth, then for every multi-index $a$, every $t\ge0$ and every $x$,
--   $$
--   \partial^a_{\mathrm{full}}v(t,x)=\partial^av(t,x).
--   $$
--
--   So for smooth fields the derivatives in the Navier–Stokes statement, which only see $t\ge0$, can be computed with ordinary derivatives.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/FieldBounds.lean#L28-L42

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

open OAI OAI.BalancedTransport OAI.BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem OAI.BalancedTransport.Geometry.fullMixedD_eq_mixedD {v : Field F} (hv : JointSmooth v) (a : MultiIndex)
    (t : ℝ) (ht : 0 ≤ t) (x : Space) : fullMixedD a v t x = mixedD a v t x := by sorry
