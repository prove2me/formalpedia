-- Prove2me | Theorems.Thm_GlobalTheory_SemisimpleCount_rank_hom_compl
-- name    : GlobalTheory.SemisimpleCount.rank_hom_compl
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:53:22.266711+00:00
-- url     : https://prove2.me/theorems/506ec8c4-05bf-4d1e-bab3-dbc515496948
-- title:
--   Semisimple Count: rank hom compl
-- statement:
--   The Semisimple Count construction uses the rank hom compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNeZeroOfRankEq.lean#L79-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNeZeroOfRankEq.lean#L79-L82

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

theorem GlobalTheory.SemisimpleCount.rank_hom_compl {U V : Submodule Rg M} (h : IsCompl U V) :
    Module.rank ℂ (S →ₗ[Rg] M) = Module.rank ℂ (S →ₗ[Rg] U) + Module.rank ℂ (S →ₗ[Rg] V) := by sorry
