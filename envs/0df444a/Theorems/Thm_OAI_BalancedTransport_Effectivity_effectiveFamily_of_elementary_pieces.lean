-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Effectivity_effectiveFamily_of_elementary_pieces
-- name    : OAI.BalancedTransport.Effectivity.effectiveFamily_of_elementary_pieces
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T05:02:43.423978+00:00
-- url     : https://prove2.me/theorems/d527c399-d6ef-4ecc-aeef-4211afadf445
-- title:
--   Families glued from elementary pieces are effective
-- statement:
--   A family $F$ assigns a velocity $F(M,w)$ to every finite machine $M$ and input $w$. It is effective when computable maps, given the code of $(M,w)$, a multi-index $a$, a rational point $(t,x)$ with $t\ge0$ and $n$, approximate $\partial^aF(M,w)(t,x)$ within $2^{-n}$. Computable bounds on $|\partial^aF(M,w)|$ and a computable support radius are also required. Let $L(p)$ and $V(p)$ be jointly smooth, elementary in $(t,x,p)$, and let $\kappa$ be computable with $|\kappa(m)_i|\le C$. Suppose each $F(M,w)$ is jointly smooth and vanishes outside the ball of radius $R$. Suppose also that, with $p=\kappa(\mathrm{code}(M,w))$,
--   $$
--   F(M,w)\approx L(p)\ \text{near each }t\in[0,1),\qquad F(M,w)\approx V(p)\bigl(\cdot-\lfloor t\rfloor\bigr)\ \text{near each }t\ge1,
--   $$
--   where $\approx$ means equality on a neighbourhood of $t$. Then $F$ is an effective family.
--
--   This is how the loading phase and the periodic template combine into effectively computable velocities and forces.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/EffectiveGluing.lean#L219-L283

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
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompiledGeometry
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryJets
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveGluing

open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity
open BalancedTransport.Geometry Set Filter
open scoped Topology

theorem OAI.BalancedTransport.Effectivity.effectiveFamily_of_elementary_pieces {d : ℕ}
    {L V : (Fin d → ℝ) → Velocity} (hL : ElementaryField L) (hV : ElementaryField V)
    (hsL : ∀p, JointSmooth (L p)) (hsV : ∀p, JointSmooth (V p))
    {κ : ℕ → Fin d → ℚ} (hκ : Computable κ) (C R : ℕ)
    (hC : ∀n i, |(κ n i : ℝ)| ≤ C) {F : Family Velocity}
    (hF : ∀M w, JointSmooth (F M w))
    (hS : ∀M w, SpatiallySupported (Metric.closedBall (0 : Space) R) (F M w))
    (hp : ElementaryPieces L V κ F) : EffectiveFamily F := by sorry
