-- Prove2me | Theorems.Thm_GlobalTheory_FactorwiseExtension_toLinearMap_update_add
-- name    : GlobalTheory.FactorwiseExtension.toLinearMap_update_add
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:17:54.573667+00:00
-- url     : https://prove2.me/theorems/11f8f4cd-ff70-4f15-9dde-5ded79f7812c
-- title:
--   Factorwise Extension: to Linear Map update add
-- statement:
--   The Factorwise Extension construction uses the to Linear Map update add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsMultilinearSlotwiseExtensionOfEquivariant.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsMultilinearSlotwiseExtensionOfEquivariant.lean#L33-L38

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

theorem GlobalTheory.FactorwiseExtension.toLinearMap_update_add (T : MultilinearMap ℂ H E) {i j : ι} (h : i ≠ j) (w : ∀ τ, H τ)
    (x y : H i) : T.toLinearMap (update w i (x + y)) j =
      T.toLinearMap (update w i x) j + T.toLinearMap (update w i y) j := by sorry
