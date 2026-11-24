-- Prove2me | Theorems.Thm_GlobalTheory_SemisimpleCount_map_mem_killed
-- name    : GlobalTheory.SemisimpleCount.map_mem_killed
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:20.701357+00:00
-- url     : https://prove2.me/theorems/efc90433-a3a9-4eea-8c2f-5d2fbd55d2d6
-- title:
--   Semisimple Count: map mem killed
-- statement:
--   The Semisimple Count construction uses the map mem killed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNeZeroOfRankEq.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNeZeroOfRankEq.lean#L20-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroOfRankEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SemisimpleCount
variable {Rg : Type} [Ring Rg] [Algebra ℂ Rg]
variable (I : Set Rg) {M N : Type} [AddCommGroup M] [Module ℂ M] [Module Rg M]
    [IsScalarTower ℂ Rg M] [AddCommGroup N] [Module ℂ N] [Module Rg N] [IsScalarTower ℂ Rg N]

theorem GlobalTheory.SemisimpleCount.map_mem_killed {A B : Type} [AddCommGroup A] [Module Rg A] [AddCommGroup B] [Module Rg B]
    (f : A →ₗ[Rg] B) {a : A} (ha : ∀ x ∈ I, x • a = 0) : ∀ x ∈ I, x • f a = 0 := by sorry
