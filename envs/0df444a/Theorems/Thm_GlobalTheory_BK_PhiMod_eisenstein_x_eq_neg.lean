-- Prove2me | Theorems.Thm_GlobalTheory_BK_PhiMod_eisenstein_x_eq_neg
-- name    : GlobalTheory.BK.PhiMod.eisenstein_x_eq_neg
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:52:19.983533+00:00
-- url     : https://prove2.me/theorems/6e3b53ed-2375-452c-bba2-565f9f7b082b
-- title:
--   Phi Mod: eisenstein x eq neg
-- statement:
--   The Phi Mod construction uses the eisenstein x eq neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqAlgebraMapAddPowMul.lean#L236-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqAlgebraMapAddPowMul.lean#L236-L238

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

theorem GlobalTheory.BK.PhiMod.eisenstein_x_eq_neg {y : Vec K a ι} (hy : y ∈ P.Mext (invE l e (A O K))) :
    (P.plus hy).EN xVec = -(P.plusInl hy).app (P.EN y - E K l e • P.zeta y) := by sorry
