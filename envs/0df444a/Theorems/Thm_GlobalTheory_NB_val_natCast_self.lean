-- Prove2me | Theorems.Thm_GlobalTheory_NB_val_natCast_self
-- name    : GlobalTheory.NB.val_natCast_self
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:15:19.243654+00:00
-- url     : https://prove2.me/theorems/765dd032-41bf-56cf-b1fe-5db4091c6b17
-- title:
--   NB: val nat Cast self
-- statement:
--   The NB construction uses the val nat Cast self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MapCSmulMulVec.lean#L82-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MapCSmulMulVec.lean#L82-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MapCSmulMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open GlobalTheory GlobalTheory.NB
attribute [instance] Fr.eeRing Fr.eeAlgA Fr.eeAlgO Fr.eeTow

theorem GlobalTheory.NB.val_natCast_self (l : ℕ) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (h0 : (l : O) ≠ 0) (h1 : ¬ IsUnit (l : O)) : val l (l : O) = 1 := by sorry
