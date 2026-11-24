-- Prove2me | Theorems.Thm_GlobalTheory_BK_PhiMod_mem_Mext_invE_of_mem_divE
-- name    : GlobalTheory.BK.PhiMod.mem_Mext_invE_of_mem_divE
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:52:31.489999+00:00
-- url     : https://prove2.me/theorems/c731395d-bb03-43df-956a-ea94113714b0
-- title:
--   Phi Mod: mem Mext inv E of mem div E
-- statement:
--   The Phi Mod construction uses the mem Mext inv E of mem div E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqAlgebraMapAddPowMul.lean#L197-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqAlgebraMapAddPowMul.lean#L197-L199

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

theorem GlobalTheory.BK.PhiMod.mem_Mext_invE_of_mem_divE {B : Subalgebra O K⟦X⟧} [HasU B] {n : ℕ} {y : Vec K a ι}
    (hy : E K l e ^ n • y ∈ P.Mext B) : y ∈ P.Mext (invE l e B) := by sorry
