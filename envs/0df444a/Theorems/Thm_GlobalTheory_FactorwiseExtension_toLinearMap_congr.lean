-- Prove2me | Theorems.Thm_GlobalTheory_FactorwiseExtension_toLinearMap_congr
-- name    : GlobalTheory.FactorwiseExtension.toLinearMap_congr
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:17:38.103154+00:00
-- url     : https://prove2.me/theorems/918113b7-758c-43f5-91e9-aa8fa55c6b98
-- title:
--   Factorwise Extension: to Linear Map congr
-- statement:
--   The Factorwise Extension construction uses the to Linear Map congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsMultilinearSlotwiseExtensionOfEquivariant.lean#L23-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsMultilinearSlotwiseExtensionOfEquivariant.lean#L23-L31

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

theorem GlobalTheory.FactorwiseExtension.toLinearMap_congr (T : MultilinearMap ℂ H E) {w w' : ∀ τ, H τ} (i : ι)
    (h : ∀ j, j ≠ i → w j = w' j) : T.toLinearMap w i = T.toLinearMap w' i := by sorry
