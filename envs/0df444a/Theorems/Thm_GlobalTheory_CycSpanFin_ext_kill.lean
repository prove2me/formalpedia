-- Prove2me | Theorems.Thm_GlobalTheory_CycSpanFin_ext_kill
-- name    : GlobalTheory.CycSpanFin.ext_kill
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:34:36.740201+00:00
-- url     : https://prove2.me/theorems/18062ac9-6b62-4f6c-9fdf-1a21062d5aa6
-- title:
--   Cyc Span Fin: ext kill
-- statement:
--   The Cyc Span Fin construction uses the ext kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteDimensionalSpanAdjoin.lean#L107-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteDimensionalSpanAdjoin.lean#L107-L118

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalSpanAdjoin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.CycSpanFin
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.CycSpanFin.ext_kill (T R : Module.End ℂ V) (d : ℕ) (hRT : Commute R T) {N : Submodule ℂ V}
    (hN : ∀ v ∈ N, R v = 0) : ∀ v ∈ ext T d N, R v = 0 := by sorry
