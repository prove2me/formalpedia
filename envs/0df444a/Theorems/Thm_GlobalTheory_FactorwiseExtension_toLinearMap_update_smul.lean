-- Prove2me | Theorems.Thm_GlobalTheory_FactorwiseExtension_toLinearMap_update_smul
-- name    : GlobalTheory.FactorwiseExtension.toLinearMap_update_smul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:17:52.202105+00:00
-- url     : https://prove2.me/theorems/9f277caa-e789-4cd7-8f95-0db3cc0898be
-- title:
--   Factorwise Extension: to Linear Map update smul
-- statement:
--   The Factorwise Extension construction uses the to Linear Map update smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsMultilinearSlotwiseExtensionOfEquivariant.lean#L40-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsMultilinearSlotwiseExtensionOfEquivariant.lean#L40-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsMultilinearSlotwiseExtensionOfEquivariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Function
open GlobalTheory GlobalTheory.FactorwiseExtension
variable {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ τ, AddCommGroup (H τ)] [∀ τ, Module ℂ (H τ)]
  {E : Type} [AddCommGroup E] [Module ℂ E]

theorem GlobalTheory.FactorwiseExtension.toLinearMap_update_smul (T : MultilinearMap ℂ H E) {i j : ι} (h : i ≠ j) (w : ∀ τ, H τ)
    (c : ℂ) (x : H i) : T.toLinearMap (update w i (c • x)) j = c • T.toLinearMap (update w i x) j := by sorry
