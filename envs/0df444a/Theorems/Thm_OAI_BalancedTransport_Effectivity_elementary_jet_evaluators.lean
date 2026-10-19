-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Effectivity_elementary_jet_evaluators
-- name    : OAI.BalancedTransport.Effectivity.elementary_jet_evaluators
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T05:01:43.696307+00:00
-- url     : https://prove2.me/theorems/6080f442-bc06-49da-8e2d-4413a6d09846
-- title:
--   Computable jets of an elementary field with computable rational parameters
-- statement:
--   Let $v(p)$ be a parametrized velocity whose components are elementary in $(t,x,p)\in\mathbb R^{4+d}$, with each $v(p)$ jointly smooth. Let $\kappa:\mathbb N\to\mathbb Q^d$ be computable with $|\kappa(m)_i|\le C$. Then there are computable $E$ and $b$ such that, for all codes $m$, multi-indices $a$, rational points $(t,x)$ and $n\in\mathbb N$:
--   $$
--   \bigl|E(m,a,(t,x),n)-\partial^a v(\kappa(m))(t,x)\bigr|\le2^{-n}\quad\text{if }|t|\le1 .
--   $$
--   Moreover $|\partial^av(\kappa(m))(t,x)|\le b(a,S)$ whenever $|t|\le1$ and $|x|\le S$.
--
--   This is the algorithmic core of effectivity: one period of the velocity can be evaluated and bounded from the machine's code.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/EffectiveGluing.lean#L145-L217

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

theorem OAI.BalancedTransport.Effectivity.elementary_jet_evaluators {d : ℕ} {v : (Fin d → ℝ) → Velocity}
    (hv : ElementaryField v) (hs : ∀ p, JointSmooth (v p))
    {κ : ℕ → Fin d → ℚ} (hκ : Computable κ) (C : ℕ)
    (hC : ∀ n i, |(κ n i : ℝ)| ≤ C) :
    ∃ E : (ℕ × MultiIndex × RationalPoint × ℕ) → Fin 3 → ℚ,
    ∃ b : MultiIndex × ℕ → ℕ,
      Computable E ∧ Computable b ∧
      (∀ m a z n, |(z.1 : ℝ)| ≤ 1 → ∀ i,
        |(E (m,a,z,n) i : ℝ) - fullMixedD a (v (fun j => (κ m j : ℝ)))
          z.1 (rationalSpace z.2) i| ≤ error n) ∧
      (∀ m a t x (S : ℕ), |t| ≤ 1 → ‖x‖ ≤ (S : ℝ) →
        ‖fullMixedD a (v (fun j => (κ m j : ℝ))) t x‖ ≤ (b (a,S) : ℝ)) := by sorry
