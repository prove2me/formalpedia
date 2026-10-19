-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Universal_post_step
-- name    : OAI.BalancedTransport.Universal.post_step
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:23:27.639216+00:00
-- url     : https://prove2.me/theorems/a7d95b8b-f7fb-48b1-a43d-7a8071dae889
-- title:
--   The finite tape machine simulates a finitely supported Turing machine step by step
-- statement:
--   Let $P$ be a Turing machine (in the standard library's model, where each instruction either writes a symbol or moves the head) over a finite alphabet. Let $S$ be a finite set of states that $P$ supports. Let $M_P$ be the finite deterministic tape machine obtained by indexing the states in $S$ and the symbols. Suppose a configuration $c$ of $P$ corresponds to a configuration $d$ of $M_P$: $c$ is in a state of $S$, the state indices agree, and every tape cell relative to the head has the matching index. Then
--   $$
--   P\text{ halts at }c\ \Rightarrow\ M_P\text{ halts at }d,\qquad c\to c'\ \Rightarrow\ \exists d',\ d\to d'\text{ and }d'\text{ corresponds to }c'.
--   $$
--
--   Hence $M_P$ halts on an input exactly when $P$ does, which lets a universal Turing machine be compiled into a finite tape machine.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/FiniteSimulator.lean#L86-L138

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

open OAI OAI.BalancedTransport OAI.BalancedTransport.Universal
open Turing StateTransition
open scoped Classical
variable {Γ Λ : Type*} [Fintype Γ] [Inhabited Γ] [Inhabited Λ]
variable (P : TM0.Machine Γ Λ) (S : Finset Λ) (ss : TM0.Supports P S)

theorem OAI.BalancedTransport.Universal.post_step (c : TM0.Cfg Γ Λ) (d : TapeConfiguration (finitePostMachine P S ss))
    (h : PostRel P S ss c d) :
    match TM0.step P c with
    | none => machineStep (finitePostMachine P S ss) d = none
    | some c' => ∃ d', machineStep (finitePostMachine P S ss) d = some d' ∧ PostRel P S ss c' d' := by sorry
