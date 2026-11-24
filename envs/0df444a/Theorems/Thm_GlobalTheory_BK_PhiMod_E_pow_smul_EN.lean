-- Prove2me | Theorems.Thm_GlobalTheory_BK_PhiMod_E_pow_smul_EN
-- name    : GlobalTheory.BK.PhiMod.E_pow_smul_EN
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:53:50.040832+00:00
-- url     : https://prove2.me/theorems/3e19609b-9119-457c-a656-8d9a49582e85
-- title:
--   Phi Mod: E pow smul EN
-- statement:
--   The Phi Mod construction uses the E pow smul EN property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqAlgebraMapAddPowMul.lean#L248-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqAlgebraMapAddPowMul.lean#L248-L257

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

theorem GlobalTheory.BK.PhiMod.E_pow_smul_EN (n : ℕ) (y : Vec K a ι) : E K l e ^ n • P.EN y =
    P.EN (E K l e ^ n • y) - ((n : K⟦X⟧) * N K (E K l e)) • E K l e ^ n • y := by sorry
