-- Prove2me | Theorems.Thm_GlobalTheory_BK_PhiMod_hatTot_sub_mem_Mhat_iff
-- name    : GlobalTheory.BK.PhiMod.hatTot_sub_mem_Mhat_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:55:43.301092+00:00
-- url     : https://prove2.me/theorems/cf4140df-5e70-52f7-88e3-50ab37572a07
-- title:
--   Phi Mod: hat Tot sub mem Mhat iff
-- statement:
--   The Phi Mod construction uses the hat Tot sub mem Mhat iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqAlgebraMapAddPowMul.lean#L286-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqAlgebraMapAddPowMul.lean#L286-L291

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapMemNonZeroDivisorsAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
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
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
open GlobalTheory.BK.PhiMod
variable (P : PhiMod O K l e a ι)
variable [Fact l.Prime]
variable [NormedAlgebra ℚ_[l] K] [NeZero e]
variable [CompleteSpace K]

theorem GlobalTheory.BK.PhiMod.hatTot_sub_mem_Mhat_iff {v w : Vec K a ι} (hv : v ∈ P.Mext (RpiE O K l e))
    (hw : w ∈ P.Mext (RpiE O K l e)) : P.hatTot v - P.hatTot w ∈ P.Mhat ↔ P.cls v = P.cls w := by sorry
