-- Prove2me | Theorems.Thm_GlobalTheory_BK_mem_shiftE
-- name    : GlobalTheory.BK.mem_shiftE
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:52:25.586508+00:00
-- url     : https://prove2.me/theorems/48383970-7279-471d-9ed4-b11f793897db
-- title:
--   BK: mem shift E
-- statement:
--   The BK construction uses the mem shift E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqAlgebraMapAddPowMul.lean#L176-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqAlgebraMapAddPowMul.lean#L176-L177

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
variable {R : Type} [Semiring R] [Module R (Vec K a ι)] [SMulCommClass R K⟦X⟧ (Vec K a ι)]
variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
omit [IsUltrametricDist K] [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.BK.mem_shiftE {i : ℤ} {W : Submodule R (Vec K a ι)} {y : Vec K a ι} :
    y ∈ shiftE l e i W ↔ Ezpow K l e (-i) • y ∈ W := by sorry
