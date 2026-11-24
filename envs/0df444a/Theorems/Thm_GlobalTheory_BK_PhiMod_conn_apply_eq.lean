-- Prove2me | Theorems.Thm_GlobalTheory_BK_PhiMod_conn_apply_eq
-- name    : GlobalTheory.BK.PhiMod.conn_apply_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:51:50.7078+00:00
-- url     : https://prove2.me/theorems/0c868556-231c-436a-ab61-1d886a9adc1d
-- title:
--   Phi Mod: conn apply eq
-- statement:
--   The Phi Mod construction uses the conn apply eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqAlgebraMapAddPowMul.lean#L328-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqAlgebraMapAddPowMul.lean#L328-L331

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
omit [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]

theorem GlobalTheory.BK.PhiMod.conn_apply_eq (v : Vec K a ι) (τ : ZMod a) (i : ι) :
    P.conn v τ i = N K (v τ i) + ∑ j, v τ j * P.conn (bas j) τ i := by sorry
