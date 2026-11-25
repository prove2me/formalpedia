-- Prove2me | Theorems.Thm_GlobalTheory_SmulMemSpanTop_exists_smul_mem_of_span_eq_top
-- name    : GlobalTheory.SmulMemSpanTop.exists_smul_mem_of_span_eq_top
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:23:58.586052+00:00
-- url     : https://prove2.me/theorems/9c06b0ab-97b2-417d-b287-b763cced540f
-- title:
--   Smul Mem Span Top: exists smul mem of span eq top
-- statement:
--   The Smul Mem Span Top construction uses the exists smul mem of span eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsSmulMemOfSpanEqTop.lean#L7-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsSmulMemOfSpanEqTop.lean#L7-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemOfSpanEqTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SmulMemSpanTop
open NumberField

theorem GlobalTheory.SmulMemSpanTop.exists_smul_mem_of_span_eq_top {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E))
    (h : Submodule.span E (↑Λ : Set (Fin n → E)) = ⊤) (v : Fin n → E) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ Λ := by sorry
