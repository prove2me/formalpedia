-- Prove2me | Theorems.Thm_GlobalTheory_exists_normOne_det_one_add_ne_zero
-- name    : GlobalTheory.exists_normOne_det_one_add_ne_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:36:13.804749+00:00
-- url     : https://prove2.me/theorems/b7ca00ee-9a8e-4654-acc6-2ba11a9b8db3
-- title:
--   Global Theory: exists norm One det one add ne zero
-- statement:
--   The Global Theory construction uses the exists norm One det one add ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsNormOneCmFieldDetOneAddNeZero.lean#L30-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsNormOneCmFieldDetOneAddNeZero.lean#L30-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsNormOneCmFieldDetOneAddNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open GlobalTheory

theorem GlobalTheory.exists_normOne_det_one_add_ne_zero : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ),
    ∃ a : L, a * (IsCMField.complexConj L : L →+* L) a = 1 ∧ ∀ σ : L →+* ℂ, (1 + σ a • X σ).det ≠ 0 := by sorry
