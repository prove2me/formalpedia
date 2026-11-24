-- Prove2me | Theorems.Thm_GlobalTheory_FrameCompletion_isInt_smul
-- name    : GlobalTheory.FrameCompletion.isInt_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:05:11.361205+00:00
-- url     : https://prove2.me/theorems/ebe140dc-7820-4b57-b252-53956e0f7bdf
-- title:
--   Frame Completion: is Int smul
-- statement:
--   The Frame Completion construction uses the is Int smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DoubledLatticePrimitiveIsotropicFrameCompletion.lean#L91-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DoubledLatticePrimitiveIsotropicFrameCompletion.lean#L91-L92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DoubledLatticePrimitiveIsotropicFrameCompletion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.FrameCompletion
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}

theorem GlobalTheory.FrameCompletion.isInt_smul {ι κ : Type} {c : L} {M : Matrix ι κ L} (hc : c ∈ intL L) (hM : IsInt M) : IsInt (c • M) := by sorry
