-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Geometry_movingBoxVelocity_jointSmooth
-- name    : OAI.BalancedTransport.Geometry.movingBoxVelocity_jointSmooth
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:10:44.987527+00:00
-- url     : https://prove2.me/theorems/f5cc910f-6cdb-4523-8f79-fb24a3b190c2
-- title:
--   Moving-box velocities are jointly smooth
-- statement:
--   Let $c,d:\mathbb R\to\mathbb R^3$ be $C^\infty$ curves with $d_i(t)\ne0$ for all $t$ and $i$. Let $a,b\in\mathbb R^3$ and $\eta\in\mathbb R$. The moving-box velocity $u$ of the box with corners $c(t)+d(t)a$ and $c(t)+d(t)b$ (products taken coordinatewise) is the curl of a box cutoff times an affine potential with translation velocity $c'(t)$ and rates $d_i'(t)/d_i(t)$. Then
--   $$
--   (t,x)\mapsto u(t,x)\ \text{ is }C^\infty\text{ on }\mathbb R\times\mathbb R^3 .
--   $$
--
--   So box motions produce velocity fields that are smooth in space and time together.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/TimeRegularity.lean#L89-L107

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

open OAI OAI.BalancedTransport OAI.BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem OAI.BalancedTransport.Geometry.movingBoxVelocity_jointSmooth {c d : ℝ → Space}
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hd : ContDiff ℝ (⊤ : ℕ∞) d)
    (hn : ∀ t i, d t i ≠ 0) (a b : Space) (η : ℝ) :
    JointSmooth (movingBoxVelocity a b c d η) := by sorry
