-- Prove2me | Theorems.Thm_GlobalTheory_BK_TameGal_norm_root
-- name    : GlobalTheory.BK.TameGal.norm_root
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:06:27.512492+00:00
-- url     : https://prove2.me/theorems/b8bff9f0-781f-450e-be18-85c60fcaa9df
-- title:
--   Tame Gal: norm root
-- statement:
--   The Tame Gal construction uses the norm root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/InstTameDescentExponentDataPadicThree.lean#L120-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/InstTameDescentExponentDataPadicThree.lean#L120-L123

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
variable [NeZero e]

theorem GlobalTheory.BK.TameGal.norm_root (g : TameGal K l e a) (τ : ZMod a) : ‖root g τ‖ = 1 := by sorry
