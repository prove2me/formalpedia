-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Recorder_guarded_period_step
-- name    : OAI.BalancedTransport.Recorder.guarded_period_step
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:53:50.614418+00:00
-- url     : https://prove2.me/theorems/30025636-3654-462f-8780-63b957bf7f9b
-- title:
--   One period of the flow performs one recorder step
-- statement:
--   The recorder is a three-stack machine that simulates a Turing machine $M$ reversibly. A configuration has a control state and three infinite stacks: left, right and history. Stack letters are work symbols $a$, marked symbols $\hat a$, a boundary marker, and records of executed transitions. Each step replaces finite prefixes of the three stacks and the control according to one row of a finite table. Let $v$ be a guarded template for $M$: for every valid row and every point $x$ of its source box, a trajectory of $v$ on $[0,1]$ carries $x$ to its image under the row's box map, avoiding the observer $(-1,2)^3$ unless the row leads to the halting ready state. Assume $v$ and the loading field have time collars, and $v(t,\cdot)$ is $L$-Lipschitz for $t\ge0$. Let $X$ be a material flow of the loaded repetition $u=u_{\mathrm{load}}+g\,\tilde v$. If the recorder steps from $c$ to $d$ and $X(n+1,a)=\mathrm{code}(c)$, then
--   $$
--   X(n+2,a)=\mathrm{code}(d),
--   $$
--   and if $d$ is not in the halting ready state, $X(t,a)$ stays outside the observer for $n+1\le t\le n+2$.
--
--   By induction over periods, the particle follows the recorder's run, one step per unit of time.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/Bridge.lean#L146-L176

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

open OAI OAI.BalancedTransport OAI.BalancedTransport.Recorder
open Set BalancedTransport.Geometry
open scoped NNReal
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ] [DecidableEq Q]
variable {M : Machine Q Γ} {v load : Velocity} {X : MaterialFlow} {L : ℝ≥0}

theorem OAI.BalancedTransport.Recorder.guarded_period_step (hg : GuardedTemplate M v) (hv : TimeCollars v)
    (hl : TimeCollars load)
    (hLip : ∀ t, 0 ≤ t → LipschitzWith L (v t))
    (hX : IsMaterialFlow (loadedRepeat load v) X)
    {c d : Configuration Q Γ} (hcd : Step M c d) (n : ℕ) (a : Space)
    (hstart : X ((n : ℝ) + 1) a = c.code M) :
    X ((n : ℝ) + 2) a = d.code M ∧
      (d.control ≠ .ready M.halt → ∀ t ∈ Icc (0 : ℝ) 1,
        X (t + ((n : ℝ) + 1)) a ∉ observer) := by sorry
