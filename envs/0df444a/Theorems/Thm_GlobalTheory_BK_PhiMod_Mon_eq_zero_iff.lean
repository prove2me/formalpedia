-- Prove2me | Theorems.Thm_GlobalTheory_BK_PhiMod_Mon_eq_zero_iff
-- name    : GlobalTheory.BK.PhiMod.Mon_eq_zero_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:54:53.97043+00:00
-- url     : https://prove2.me/theorems/7f2836ea-ba62-43ad-a27f-c0867c8b14b8
-- title:
--   Phi Mod: Mon eq zero iff
-- statement:
--   The Phi Mod construction uses the Mon eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqAlgebraMapAddPowMul.lean#L240-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqAlgebraMapAddPowMul.lean#L240-L243

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

theorem GlobalTheory.BK.PhiMod.Mon_eq_zero_iff {y : Vec K a ι} (hy : y ∈ P.Mext (invE l e (A O K))) :
    P.Mon y = 0 ↔ (P.plus hy).EN xVec ∈ (P.plus hy).Man := by sorry
