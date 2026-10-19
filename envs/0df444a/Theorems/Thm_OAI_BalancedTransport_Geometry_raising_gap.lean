-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Geometry_raising_gap
-- name    : OAI.BalancedTransport.Geometry.raising_gap
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:35:03.989528+00:00
-- url     : https://prove2.me/theorems/6378565a-9ed4-45e1-a8a6-c899d1413931
-- title:
--   Raising a point vertically keeps it separated from points below
-- statement:
--   Let $p,q\in\mathbb R^3$ with $q_1\le p_1\le H$, and let $D\in\mathbb R$. Suppose $|p_k-q_k|>D$ for some coordinate $k$. Let $p'$ be $p$ with its coordinate $1$ replaced by $H$, and let $r\in[0,1]$. Then some coordinate $k'$ satisfies
--   $$
--   \bigl|(1-r)p_{k'}+r\,p'_{k'}-q_{k'}\bigr|>D .
--   $$
--
--   When a box centre is raised in the $x_1$ direction, it stays separated from every centre that is not above it, so boxes can be lifted to parking positions without collisions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/Parking.lean#L72-L86

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

open OAI OAI.BalancedTransport OAI.BalancedTransport.Geometry
open Set
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem OAI.BalancedTransport.Geometry.raising_gap {p q : Space} {H r D : ℝ} (hq : q 1 ≤ p 1) (hH : p 1 ≤ H)
    (hr : r ∈ Icc (0 : ℝ) 1) (hgap : ∃ k, D < |p k - q k|) :
    ∃ k, D < |(1 - r) * p k + r * (Function.update p 1 H) k - q k| := by sorry
