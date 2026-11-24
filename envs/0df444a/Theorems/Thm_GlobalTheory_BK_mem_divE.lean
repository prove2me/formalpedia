-- Prove2me | Theorems.Thm_GlobalTheory_BK_mem_divE
-- name    : GlobalTheory.BK.mem_divE
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:51:32.786265+00:00
-- url     : https://prove2.me/theorems/9868a31d-0350-475e-bb30-b3efa39a3406
-- title:
--   BK: mem div E
-- statement:
--   The BK construction uses the mem div E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqAlgebraMapAddPowMul.lean#L162-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqAlgebraMapAddPowMul.lean#L162-L163

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
omit [IsUltrametricDist K] [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.BK.mem_divE {n : ℕ} {W : Submodule R (Vec K a ι)} {y : Vec K a ι} :
    y ∈ divE l e n W ↔ E K l e ^ n • y ∈ W := by sorry
