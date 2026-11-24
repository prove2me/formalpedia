-- Prove2me | Theorems.Thm_GlobalTheory_FrameCompletion_isInt_fromCols
-- name    : GlobalTheory.FrameCompletion.isInt_fromCols
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:05:27.015722+00:00
-- url     : https://prove2.me/theorems/15b5e815-cc08-463f-bec5-72fda7f75133
-- title:
--   Frame Completion: is Int from Cols
-- statement:
--   The Frame Completion construction uses the is Int from Cols property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DoubledLatticePrimitiveIsotropicFrameCompletion.lean#L110-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DoubledLatticePrimitiveIsotropicFrameCompletion.lean#L110-L113

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

theorem GlobalTheory.FrameCompletion.isInt_fromCols {ι κ κ' : Type} {A : Matrix ι κ L} {B : Matrix ι κ' L} (hA : IsInt A) (hB : IsInt B) :
    IsInt (fromCols A B) := by sorry
