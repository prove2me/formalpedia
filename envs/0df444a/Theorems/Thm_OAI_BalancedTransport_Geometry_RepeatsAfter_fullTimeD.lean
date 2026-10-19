-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Geometry_RepeatsAfter_fullTimeD
-- name    : OAI.BalancedTransport.Geometry.RepeatsAfter.fullTimeD
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:11:57.822681+00:00
-- url     : https://prove2.me/theorems/3a3a6453-3eaf-4ded-a0a4-d44ebe4dcd5b
-- title:
--   Time derivatives of eventually periodic fields are eventually periodic
-- statement:
--   A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, with values in a normed space. It is jointly smooth when $(t,x)\mapsto v(t,x)$ is $C^\infty$. Suppose $v$ is jointly smooth and repeats after $T$, meaning $v(t+1,\cdot)=v(t,\cdot)$ for all $t\ge T$. Then
--   $$
--   \partial_tv(t+1,x)=\partial_tv(t,x)\qquad(t\ge T,\ x\in\mathbb R^3).
--   $$
--
--   Iterating this, every full mixed derivative of an eventually periodic smooth field is eventually periodic with the same onset.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/FieldBounds.lean#L86-L99

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

theorem OAI.BalancedTransport.Geometry.RepeatsAfter.fullTimeD {T : ℝ} {v : Field F} (h : RepeatsAfter T v)
    (hv : JointSmooth v) : RepeatsAfter T (fullTimeD v) := by sorry
