-- Prove2me | Theorems.Thm_GlobalTheory_BK_TameGal_root_ne_zero
-- name    : GlobalTheory.BK.TameGal.root_ne_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:56:39.266124+00:00
-- url     : https://prove2.me/theorems/595f4e45-41c6-5d6c-8153-9c0d522e7573
-- title:
--   Tame Gal: root ne zero
-- statement:
--   The Tame Gal construction uses the root ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/InstTameDescentExponentDataPadicThree.lean#L116-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/InstTameDescentExponentDataPadicThree.lean#L116-L116

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
open GlobalTheory.BK.TameGal
variable {l}

theorem GlobalTheory.BK.TameGal.root_ne_zero (g : TameGal K l e a) (τ : ZMod a) : root g τ ≠ 0 := by sorry
