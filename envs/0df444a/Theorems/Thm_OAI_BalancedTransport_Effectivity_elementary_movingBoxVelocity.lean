-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Effectivity_elementary_movingBoxVelocity
-- name    : OAI.BalancedTransport.Effectivity.elementary_movingBoxVelocity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:39:12.627624+00:00
-- url     : https://prove2.me/theorems/e664e949-c9a0-4405-a4b7-950ac39e3bca
-- title:
--   Moving-box velocities with elementary motion are elementary
-- statement:
--   A parametrized field $f(p)(t,x)$, with $p\in\mathbb R^d$, is elementary when each component of $(t,x,p)\mapsto f(p)(t,x)$ is computed on $\mathbb R^{4+d}$ by a straight-line numeric program. The program is built from rational constants, coordinates, sums, products, negation, guarded inverses, $\exp$, logarithms of rationals and derivatives of $e^{-1/x}$. Let $a,b\in\mathbb Q^3$ and $\eta\in\mathbb Q$. Let $c(p,t)$ and $w(p,t)$ be elementary curves in $\mathbb R^3$, depending on parameters, with each $w_i\ge\frac1{n_i+1}$ for some $n_i\in\mathbb N$. Then the parametrized moving-box velocity
--   $$
--   p\mapsto u_p,\qquad u_p=\text{the velocity of the box }c(p,t)+w(p,t)[a,b]\text{ with margin }\eta,
--   $$
--   is elementary.
--
--   So the velocity fields of elementary box motions can be evaluated and differentiated by algorithms.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/ElementaryFields.lean#L142-L158

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

open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity
open BalancedTransport.Geometry

theorem OAI.BalancedTransport.Effectivity.elementary_movingBoxVelocity {d : ℕ} (a b : Space) (ar : ∀i, RationalConstant (a i))
    (br : ∀i, RationalConstant (b i)) {c w : (Fin d → ℝ) → ℝ → Space}
    (hc : ElementaryField (fun p t _ => c p t)) (hw : ElementaryField (fun p t _ => w p t))
    (hn : ∀ i, ∃ n : ℕ, ∀ p t, ((n+1:ℕ):ℝ)⁻¹ ≤ w p t i)
    {η : ℝ} (ηr : RationalConstant η) : ElementaryField (fun p => movingBoxVelocity a b (c p) (w p) η) := by sorry
