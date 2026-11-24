-- Prove2me | Theorems.Thm_GlobalTheory_CycSpanFin_le_ext
-- name    : GlobalTheory.CycSpanFin.le_ext
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:34:22.115808+00:00
-- url     : https://prove2.me/theorems/83002310-240f-4ce2-a9c9-e37c21b71c3a
-- title:
--   Cyc Span Fin: le ext
-- statement:
--   The Cyc Span Fin construction uses the le ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteDimensionalSpanAdjoin.lean#L53-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteDimensionalSpanAdjoin.lean#L53-L54

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

theorem GlobalTheory.CycSpanFin.le_ext (T : Module.End ℂ V) (d : ℕ) (N : Submodule ℂ V) : N ≤ ext T d N := by sorry
