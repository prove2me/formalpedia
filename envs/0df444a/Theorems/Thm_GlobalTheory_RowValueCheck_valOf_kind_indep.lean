-- Prove2me | Theorems.Thm_GlobalTheory_RowValueCheck_valOf_kind_indep
-- name    : GlobalTheory.RowValueCheck.valOf_kind_indep
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:20:40.924229+00:00
-- url     : https://prove2.me/theorems/ff50030a-ed4c-5f88-b1b3-11b512255df6
-- title:
--   Row Value Check: val Of kind indep
-- statement:
--   The Row Value Check construction uses the val Of kind indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/ValOfKindIndep.lean#L137-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/ValOfKindIndep.lean#L137-L171

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

theorem GlobalTheory.RowValueCheck.valOf_kind_indep [NeZero d] (X : RowData C V d I J) {N : ℕ}
    (P : MvPolynomial (Fin N × WV I) C) (k k' : Fin N → Option (Fin 2 × ZMod d × ZMod d))
    (hk : RowsOK X.G X.Alt P k) (hk' : RowsOK X.G X.Alt P k')
    (gr : Fin N → MvPowerSeries (WV I) C) : ValOf X.hL P k gr = ValOf X.hL P k' gr := by sorry
