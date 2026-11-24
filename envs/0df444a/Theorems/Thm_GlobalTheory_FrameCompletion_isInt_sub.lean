-- Prove2me | Theorems.Thm_GlobalTheory_FrameCompletion_isInt_sub
-- name    : GlobalTheory.FrameCompletion.isInt_sub
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:04:57.173443+00:00
-- url     : https://prove2.me/theorems/1cd3e2a8-fd47-4d65-a798-423e4cf53c5f
-- title:
--   Frame Completion: is Int sub
-- statement:
--   The Frame Completion construction uses the is Int sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DoubledLatticePrimitiveIsotropicFrameCompletion.lean#L96-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DoubledLatticePrimitiveIsotropicFrameCompletion.lean#L96-L97

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

theorem GlobalTheory.FrameCompletion.isInt_sub {ι κ : Type} {M N : Matrix ι κ L} (hM : IsInt M) (hN : IsInt N) : IsInt (M - N) := by sorry
