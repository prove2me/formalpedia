-- Prove2me | Theorems.Thm_GlobalTheory_BK_Hom_onPol_Mon
-- name    : GlobalTheory.BK.Hom.onPol_Mon
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:56:17.079031+00:00
-- url     : https://prove2.me/theorems/58f8ecb7-8f18-44c4-b1d9-bfb9a13812b9
-- title:
--   Hom: on Pol Mon
-- statement:
--   The Hom construction uses the on Pol Mon property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqAlgebraMapAddPowMul.lean#L361-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqAlgebraMapAddPowMul.lean#L361-L362

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
open GlobalTheory.BK.Hom
variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
  {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : Hom P Q)

theorem GlobalTheory.BK.Hom.onPol_Mon (y : Vec K a ι) : F.onPol (P.Mon y) = Q.Mon (F.app y) := by sorry
