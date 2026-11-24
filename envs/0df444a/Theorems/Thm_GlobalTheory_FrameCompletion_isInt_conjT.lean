-- Prove2me | Theorems.Thm_GlobalTheory_FrameCompletion_isInt_conjT
-- name    : GlobalTheory.FrameCompletion.isInt_conjT
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:51:27.301868+00:00
-- url     : https://prove2.me/theorems/2fbddbf8-4878-4918-9cfc-bf69caddd6e8
-- title:
--   Frame Completion: is Int conj T
-- statement:
--   The Frame Completion construction uses the is Int conj T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DoubledLatticePrimitiveIsotropicFrameCompletion.lean#L99-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DoubledLatticePrimitiveIsotropicFrameCompletion.lean#L99-L103

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

theorem GlobalTheory.FrameCompletion.isInt_conjT (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {ι κ : Type} {M : Matrix ι κ L} (hM : IsInt M) :
    IsInt (cT σ M) := by sorry
