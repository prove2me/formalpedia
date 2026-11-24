-- Prove2me | Theorems.Thm_GlobalTheory_SemisimpleCount_exists_simple
-- name    : GlobalTheory.SemisimpleCount.exists_simple
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:53:21.635067+00:00
-- url     : https://prove2.me/theorems/c934fcca-42a3-41fb-ab97-8bd7dddc22a9
-- title:
--   Semisimple Count: exists simple
-- statement:
--   The Semisimple Count construction uses the exists simple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNeZeroOfRankEq.lean#L117-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNeZeroOfRankEq.lean#L117-L130

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

theorem GlobalTheory.SemisimpleCount.exists_simple {A : Type} [AddCommGroup A] [Module Rg A] [IsSemisimpleModule Rg A]
    {a : A} (ha : a ≠ 0) (hI : ∀ x ∈ I, x • a = 0) :
    ∃ U : Submodule Rg A, IsSimpleModule Rg U ∧ ∃ u : U, u ≠ 0 ∧ ∀ x ∈ I, x • u = 0 := by sorry
