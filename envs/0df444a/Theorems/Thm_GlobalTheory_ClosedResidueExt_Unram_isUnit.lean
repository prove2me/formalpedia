-- Prove2me | Theorems.Thm_GlobalTheory_ClosedResidueExt_Unram_isUnit
-- name    : GlobalTheory.ClosedResidueExt.Unram.isUnit
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:13:11.742464+00:00
-- url     : https://prove2.me/theorems/a8c079ec-6bd3-431c-8284-a3e02c210b84
-- title:
--   Unram: is Unit
-- statement:
--   The Unram construction uses the is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIntegralExtIsAlgClosedResidueField.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIntegralExtIsAlgClosedResidueField.lean#L13-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIntegralExtIsAlgClosedResidueField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ClosedResidueExt
open Polynomial IsLocalRing
variable {W Ω : Type} [CommRing W] [Field Ω] [Algebra W Ω]

theorem GlobalTheory.ClosedResidueExt.Unram.isUnit {R : Subalgebra W Ω} {u : Ω} (hu : u ∈ R) (hu' : u⁻¹ ∈ R) (h0 : u ≠ 0) :
    IsUnit (⟨u, hu⟩ : R) := by sorry
