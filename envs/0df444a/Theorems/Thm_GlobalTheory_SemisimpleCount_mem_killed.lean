-- Prove2me | Theorems.Thm_GlobalTheory_SemisimpleCount_mem_killed
-- name    : GlobalTheory.SemisimpleCount.mem_killed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:35.953802+00:00
-- url     : https://prove2.me/theorems/a5a82255-3830-45d4-9c0b-ff3f35ca522c
-- title:
--   Semisimple Count: mem killed
-- statement:
--   The Semisimple Count construction uses the mem killed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNeZeroOfRankEq.lean#L18-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNeZeroOfRankEq.lean#L18-L18

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

theorem GlobalTheory.SemisimpleCount.mem_killed {m : M} : m ∈ killed I M ↔ ∀ x ∈ I, x • m = 0 := by sorry
