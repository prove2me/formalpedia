-- Prove2me | Theorems.Thm_GlobalTheory_RowValueCheck_agree_hOf_zero
-- name    : GlobalTheory.RowValueCheck.agree_hOf_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:13:26.656046+00:00
-- url     : https://prove2.me/theorems/569c1281-7cee-4c11-a4a8-ddf76b36f196
-- title:
--   Row Value Check: agree h Of zero
-- statement:
--   The Row Value Check construction uses the agree h Of zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/ValOfKindIndep.lean#L110-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/ValOfKindIndep.lean#L110-L120

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

theorem GlobalTheory.RowValueCheck.agree_hOf_zero [NeZero d] (X : RowData C V d I J) (T : Set (WV I)) (g0 : Fin 2)
    (hT : ∀ w ∈ T, w.1 = g0) (k : Option (Fin 2 × ZMod d × ZMod d)) : Agree T (hOf X.hL k) 0 := by sorry
