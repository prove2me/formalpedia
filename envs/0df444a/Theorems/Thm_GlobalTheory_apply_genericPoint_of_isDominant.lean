-- Prove2me | Theorems.Thm_GlobalTheory_apply_genericPoint_of_isDominant
-- name    : GlobalTheory.apply_genericPoint_of_isDominant
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:13:05.720802+00:00
-- url     : https://prove2.me/theorems/c740686c-8603-4d63-a7de-f2903c94e6a6
-- title:
--   Global Theory: apply generic Point of is Dominant
-- statement:
--   The Global Theory construction uses the apply generic Point of is Dominant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/BijectiveAlgebraMapIntegralClosureOfBirational.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/BijectiveAlgebraMapIntegralClosureOfBirational.lean#L34-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology
open GlobalTheory
universe u
variable {X Y : Scheme.{u}}
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology
variable {X Y : Scheme.{u}}

theorem GlobalTheory.apply_genericPoint_of_isDominant (f : X ⟶ Y) [IsDominant f] [IrreducibleSpace X]
    [IrreducibleSpace Y] : f (genericPoint X) = genericPoint Y := by sorry
