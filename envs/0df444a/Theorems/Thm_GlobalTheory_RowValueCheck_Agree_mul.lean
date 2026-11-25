-- Prove2me | Theorems.Thm_GlobalTheory_RowValueCheck_Agree_mul
-- name    : GlobalTheory.RowValueCheck.Agree.mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:15:13.768889+00:00
-- url     : https://prove2.me/theorems/fbeb3f57-d8c3-4773-9937-a03a007468be
-- title:
--   Agree: mul
-- statement:
--   The Agree construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/ValOfKindIndep.lean#L45-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/ValOfKindIndep.lean#L45-L52

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_ValOfKindIndep
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open GlobalTheory GlobalTheory.RowValueCheck
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]

theorem GlobalTheory.RowValueCheck.Agree.mul {σ : Type} {S : Set σ} {F F' K K' : MvPowerSeries σ C} (h : Agree S F F')
    (h' : Agree S K K') : Agree S (F * K) (F' * K') := by sorry
