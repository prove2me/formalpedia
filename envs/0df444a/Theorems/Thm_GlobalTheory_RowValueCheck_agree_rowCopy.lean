-- Prove2me | Theorems.Thm_GlobalTheory_RowValueCheck_agree_rowCopy
-- name    : GlobalTheory.RowValueCheck.agree_rowCopy
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:14:16.274581+00:00
-- url     : https://prove2.me/theorems/9eef158a-da1d-4161-b04d-4e01b2b8f9b9
-- title:
--   Row Value Check: agree row Copy
-- statement:
--   The Row Value Check construction uses the agree row Copy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/ValOfKindIndep.lean#L73-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/ValOfKindIndep.lean#L73-L95

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_ValOfKindIndep
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

theorem GlobalTheory.RowValueCheck.agree_rowCopy {N : ℕ} (S : Set (Fin N × WV I)) (ρ : Fin N) (F F' : MvPowerSeries (WV I) C)
    (h : Agree {w | (ρ, w) ∈ S} F F') : Agree S (rowCopy ρ F) (rowCopy ρ F') := by sorry
