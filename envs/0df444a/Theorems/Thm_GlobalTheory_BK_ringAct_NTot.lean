-- Prove2me | Theorems.Thm_GlobalTheory_BK_ringAct_NTot
-- name    : GlobalTheory.BK.ringAct_NTot
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:06:28.362416+00:00
-- url     : https://prove2.me/theorems/57ac20a8-485f-4629-a591-6e975d3330fa
-- title:
--   BK: ring Act NTot
-- statement:
--   The BK construction uses the ring Act NTot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/InstTameDescentExponentDataPadicThree.lean#L171-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/InstTameDescentExponentDataPadicThree.lean#L171-L175

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {K : Type} [NormedField K] (l : ℕ) {e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
  [NeZero a] [TameDescentExponentData K l e a]
variable {l}

theorem GlobalTheory.BK.ringAct_NTot (g : TameGal K l e a) (f : ZMod a → K⟦X⟧) :
    ringAct g (NTot f) = NTot (ringAct g f) := by sorry
