-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Effectivity_NumericOp_estimate
-- name    : OAI.BalancedTransport.Effectivity.NumericOp.estimate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:24:01.212054+00:00
-- url     : https://prove2.me/theorems/0c205001-cc55-428e-b84e-8280b2521e62
-- title:
--   Error propagation through one numeric operation
-- statement:
--   A numeric operation is one step of a straight-line program. Reading registers $s_a,s_b$ of a register list $s$ and parameters $q\in\mathbb Q$ and $a,b\in\mathbb N$, it produces one of: $q$, a coordinate $x_a$, $s_a+s_b$, $s_as_b$, $-s_a$, $s_a^{-1}$ (valid only when $s_a\ge\frac1{b+1}$), $\rho^{(a)}(s_b)$ with $\rho(x)=e^{-1/x}$, $e^{s_a}$, or $\log q$. Let $x\in\mathbb Q^d$ with $|x_i|\le C$. Suppose the real registers $s$, rational registers $\hat s$ and bound pairs $(B_j,E_j)$ satisfy $|s_j|\le B_j$ and $|\hat s_j-s_j|\le E_j2^{-p}$ for all $j$, and the operation is valid on $s$. Let $(B,E)$ be the bound pair the operation computes. Then its real value $y$ and its rational value $\hat y$ at precision $p$ satisfy
--   $$
--   |y|\le B,\qquad|\hat y-y|\le E\,2^{-p}.
--   $$
--
--   By induction along a program, the approximation computed at precision $n+E$ is within $2^{-n}$ of the true value.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/NumericBounds.lean#L49-L158

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

open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity OAI.BalancedTransport.Effectivity.NumericOp

theorem OAI.BalancedTransport.Effectivity.NumericOp.estimate (d : ℕ) [NeZero d] (o : NumericOp) (x : Fin d → ℚ)
    (p C : ℕ) (s : List ℝ) (q : List ℚ) (b : List (ℕ × ℕ))
    (hi : ∀ i, |(x i : ℝ)| ≤ C) (hb : RegisterEstimate p s q b) (hv : Valid o s) :
    |real d o (fun i => (x i : ℝ)) s| ≤ ((bound o C b).1 : ℝ) ∧
    |(rational d o x p q : ℝ) - real d o (fun i => (x i : ℝ)) s| ≤
      ((bound o C b).2 : ℝ) * error p := by sorry
