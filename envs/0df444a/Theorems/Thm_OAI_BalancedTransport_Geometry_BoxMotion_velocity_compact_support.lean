-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Geometry_BoxMotion_velocity_compact_support
-- name    : OAI.BalancedTransport.Geometry.BoxMotion.velocity_compact_support
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:57:42.938661+00:00
-- url     : https://prove2.me/theorems/c706d1fa-2bc5-4ed8-bedf-adfb627b9400
-- title:
--   Box-motion velocities have compact spatial support
-- statement:
--   A box motion from layout $A$ to layout $B$ moves box $i$ smoothly, with centre $c_i(s)$ and half-widths $w_i(s)$, from its position in $A$ (for $s\le0$) to its position in $B$ (for $s\ge1$). Volumes are constant along the way, the boxes stay $\eta$-separated, and boxes with safe indices stay in $\{x_0>2\}$. Its velocity at time $t$ is the sum of the moving-box velocities of the boxes at time $s=2t-\frac12$, so the motion happens during $\frac14\le t\le\frac34$. If $\eta>0$, then there is a compact $K\subseteq\mathbb R^3$ with
--   $$
--   u(t,x)=0\qquad\text{for all }t\text{ and all }x\notin K .
--   $$
--
--   This gives the common compact support of the velocity and the forces in the main theorem.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/MotionField.lean#L231-L251

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
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ComputabilityRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineRecursion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FiniteSimulator
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_UniversalInput
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericEvaluation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericDifferentiation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericScopes
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericJets
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericAlgebra
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Elementary
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergyCurve
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Sobolev
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergySlice
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Loading
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Periodic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Motion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Parking
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Deformation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryMotion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryCalculus
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderSimulation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineHalting
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Bridge
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MotionField

open OAI OAI.BalancedTransport OAI.BalancedTransport.Geometry OAI.BalancedTransport.Geometry.BoxMotion
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]
variable {A B : BoxLayout ι} {safe : Set ι} {η : ℝ}

theorem OAI.BalancedTransport.Geometry.BoxMotion.velocity_compact_support (m : BoxMotion A B safe η) (hη : 0 < η) :
    ∃ K : Set Space, IsCompact K ∧ SpatiallySupported K m.velocity := by sorry
