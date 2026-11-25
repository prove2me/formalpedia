-- Prove2me | Theorems.Thm_GlobalTheory_BK_TameGal_fr_mul_inertia
-- name    : GlobalTheory.BK.TameGal.fr_mul_inertia
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:56:26.263185+00:00
-- url     : https://prove2.me/theorems/97960d14-d242-4ac1-8e76-a5909fcdc0e0
-- title:
--   Tame Gal: fr mul inertia
-- statement:
--   The Tame Gal construction uses the fr mul inertia property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/InstTameDescentExponentDataPadicThree.lean#L110-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/InstTameDescentExponentDataPadicThree.lean#L110-L114

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

theorem GlobalTheory.BK.TameGal.fr_mul_inertia (ζ : rootsOfUnity e K) :
    (fr : TameGal K l e a) * inertia ζ = inertia (ζ ^ l) * fr := by sorry
