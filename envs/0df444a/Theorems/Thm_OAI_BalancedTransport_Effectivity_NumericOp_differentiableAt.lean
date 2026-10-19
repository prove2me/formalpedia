-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Effectivity_NumericOp_differentiableAt
-- name    : OAI.BalancedTransport.Effectivity.NumericOp.differentiableAt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:25:35.304773+00:00
-- url     : https://prove2.me/theorems/5b0fac78-80d0-4b5e-b284-7719c5e244a6
-- title:
--   Differentiability of one numeric operation
-- statement:
--   A numeric operation is one step of a straight-line program. Reading registers $s_a,s_b$ of a register list $s$ and parameters $q\in\mathbb Q$ and $a,b\in\mathbb N$, it produces one of: $q$, a coordinate $x_a$, $s_a+s_b$, $s_as_b$, $-s_a$, $s_a^{-1}$ (valid only when $s_a\ge\frac1{b+1}$), $\rho^{(a)}(s_b)$ with $\rho(x)=e^{-1/x}$, $e^{s_a}$, or $\log q$. Let $x\in\mathbb R^d$, and let $y\mapsto s(y)$ be register lists depending on $y\in\mathbb R^d$ whose entries are differentiable at $x$. If the operation is valid on $s(x)$, then
--   $$
--   y\mapsto\text{the real value of the operation at }(y,s(y))
--   $$
--   is differentiable at $x$.
--
--   By induction along a program, functions computed by valid programs are differentiable.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/NumericDifferentiation.lean#L97-L112

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

open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity OAI.BalancedTransport.Effectivity.NumericOp
variable (d : ℕ) [NeZero d]

theorem OAI.BalancedTransport.Effectivity.NumericOp.differentiableAt (o : NumericOp) (x : Fin d → ℝ)
    (s : (Fin d → ℝ) → List ℝ)
    (hs : ∀ a, DifferentiableAt ℝ (fun y => (s y).getD a 0) x)
    (hv : o.Valid (s x)) : DifferentiableAt ℝ (fun y => o.real d y (s y)) x := by sorry
