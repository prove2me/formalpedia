-- Prove2me | Theorems.Thm_GlobalTheory_NB_valTop_zero
-- name    : GlobalTheory.NB.valTop_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:15:14.68802+00:00
-- url     : https://prove2.me/theorems/049a2810-838b-582e-86d9-55641eba8438
-- title:
--   NB: val Top zero
-- statement:
--   The NB construction uses the val Top zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MapCSmulMulVec.lean#L76-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MapCSmulMulVec.lean#L76-L77

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

theorem GlobalTheory.NB.valTop_zero (l : ℕ) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    valTop l (0 : O) = ⊤ := by sorry
