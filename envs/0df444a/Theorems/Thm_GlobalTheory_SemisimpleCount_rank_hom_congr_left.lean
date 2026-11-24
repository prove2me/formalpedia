-- Prove2me | Theorems.Thm_GlobalTheory_SemisimpleCount_rank_hom_congr_left
-- name    : GlobalTheory.SemisimpleCount.rank_hom_congr_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:32.215506+00:00
-- url     : https://prove2.me/theorems/e2ce08f3-c288-4869-93e7-b5db6f36def3
-- title:
--   Semisimple Count: rank hom congr left
-- statement:
--   The Semisimple Count construction uses the rank hom congr left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNeZeroOfRankEq.lean#L84-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNeZeroOfRankEq.lean#L84-L92

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
variable {S : Type} [AddCommGroup S] [Module Rg S]

theorem GlobalTheory.SemisimpleCount.rank_hom_congr_left {S' : Type} [AddCommGroup S'] [Module Rg S'] (e : S ≃ₗ[Rg] S') :
    Module.rank ℂ (S →ₗ[Rg] M) = Module.rank ℂ (S' →ₗ[Rg] M) := by sorry
