-- Prove2me | Theorems.Thm_GlobalTheory_BK_exists_eq_algebraMap_add_pow_mul
-- name    : GlobalTheory.BK.exists_eq_algebraMap_add_pow_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:52:31.903158+00:00
-- url     : https://prove2.me/theorems/8b1b95ef-f237-40d7-8fc8-044ab62f8555
-- title:
--   BK: exists eq algebra Map add pow mul
-- statement:
--   The BK construction uses the exists eq algebra Map add pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqAlgebraMapAddPowMul.lean#L75-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqAlgebraMapAddPowMul.lean#L75-L90

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
variable (l e) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]

theorem GlobalTheory.BK.exists_eq_algebraMap_add_pow_mul {B : Type} [CommRing B] (s : B) (n : ℕ)
    (x : AdicCompletion (Ideal.span {s}) B) :
    ∃ (g : B) (x' : AdicCompletion (Ideal.span {s}) B),
      x = algebraMap B _ g + algebraMap B _ s ^ n * x' := by sorry
