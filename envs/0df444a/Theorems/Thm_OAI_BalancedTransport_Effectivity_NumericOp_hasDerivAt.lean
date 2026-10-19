-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Effectivity_NumericOp_hasDerivAt
-- name    : OAI.BalancedTransport.Effectivity.NumericOp.hasDerivAt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:24:42.822892+00:00
-- url     : https://prove2.me/theorems/77c1a6a5-a5b2-4c15-954b-09828508aaa7
-- title:
--   Chain rule for one numeric operation along a coordinate line
-- statement:
--   A numeric operation is one step of a straight-line program. Reading registers $s_a,s_b$ of a register list $s$ and parameters $q\in\mathbb Q$ and $a,b\in\mathbb N$, it produces one of: $q$, a coordinate $x_a$, $s_a+s_b$, $s_as_b$, $-s_a$, $s_a^{-1}$ (valid only when $s_a\ge\frac1{b+1}$), $\rho^{(a)}(s_b)$ with $\rho(x)=e^{-1/x}$, $e^{s_a}$, or $\log q$. Let $t\mapsto x(t)\in\mathbb R^d$ have derivative $e_k$ (the $k$-th unit vector) at $t$. Let $t\mapsto s(t)$ be register lists whose entries have derivatives $v_a$ at $t$, and suppose the operation is valid on $s(t)$. Then $t\mapsto y(t)$, the real value of the operation at $(x(t),s(t))$, has a derivative at $t$, given by the forward-mode rule
--   $$
--   y'(t)=\mathrm{diff}_k\bigl(s(t),v\bigr).
--   $$
--   The rule gives $0$ for literals and logarithms, $[a=k]$ for coordinates, $v_a+v_b$, $v_as_b+s_av_b$, $-v_a$, $-v_as_a^{-2}$, $\rho^{(a+1)}(s_b)v_b$ and $e^{s_a}v_a$.
--
--   These are the rules used to transform programs into programs for their partial derivatives.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/NumericDifferentiation.lean#L23-L42

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

theorem OAI.BalancedTransport.Effectivity.NumericOp.hasDerivAt (k : Fin d) (o : NumericOp) (x : ℝ → Fin d → ℝ)
    (s : ℝ → List ℝ) (v : ℕ → ℝ) (t : ℝ)
    (hx : ∀ i, HasDerivAt (fun t => x t i) (if i = k then 1 else 0) t)
    (hs : ∀ a, HasDerivAt (fun t => (s t).getD a 0) (v a) t)
    (hv : o.Valid (s t)) :
    HasDerivAt (fun t => o.real d (x t) (s t))
      (o.differential d k (fun a => (s t).getD a 0) v) t := by sorry
