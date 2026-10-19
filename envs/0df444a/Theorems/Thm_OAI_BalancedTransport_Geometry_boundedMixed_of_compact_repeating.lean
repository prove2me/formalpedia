-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Geometry_boundedMixed_of_compact_repeating
-- name    : OAI.BalancedTransport.Geometry.boundedMixed_of_compact_repeating
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:12:38.959979+00:00
-- url     : https://prove2.me/theorems/0711ab02-f453-4ea9-bb9c-95b49965f65c
-- title:
--   Smooth compactly supported eventually periodic fields have bounded derivatives
-- statement:
--   A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, with values in a normed space. It is jointly smooth when $(t,x)\mapsto v(t,x)$ is $C^\infty$. A multi-index is a list whose entries are either time or a spatial direction. The mixed derivative $\partial^av$ applies the corresponding derivatives in order, where the time derivative used on the solution side is the one-sided derivative within $[0,\infty)$; the full mixed derivative uses the ordinary time derivative instead. Let $K\subseteq\mathbb R^3$ be compact and let $v$ be jointly smooth, zero outside $K$ at all times, and $1$-periodic after time $1$. Then for every multi-index $a$ there is $C\ge0$ with
--   $$
--   \|\partial^av(t,x)\|\le C\qquad(t\ge0,\ x\in\mathbb R^3).
--   $$
--
--   This gives the uniform bounds on all mixed derivatives required of the velocity and the forces.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/FieldBounds.lean#L131-L147

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

theorem OAI.BalancedTransport.Geometry.boundedMixed_of_compact_repeating {K : Set Space} (hK : IsCompact K)
    {v : Field F} (hv : JointSmooth v) (hs : SpatiallySupported K v)
    (hp : RepeatsAfter 1 v) : BoundedMixed v := by sorry
