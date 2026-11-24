-- Prove2me | Theorems.Thm_GlobalTheory_BK_mxInv_rankOne_eq
-- name    : GlobalTheory.BK.mxInv_rankOne_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:29:30.650377+00:00
-- url     : https://prove2.me/theorems/067e2e70-0172-4d20-8589-63a52566f164
-- title:
--   BK: mx Inv rank One eq
-- statement:
--   The BK construction uses the mx Inv rank One eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqMulAddOfIsAdicComplete.lean#L137-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqMulAddOfIsAdicComplete.lean#L137-L142

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TameDescentExtendedActionExtraVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemSpanLPowSIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
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
  [IsUnitBall O K] (l e : ℕ) {a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
variable {l e}

theorem GlobalTheory.BK.mxInv_rankOne_eq (j : ZMod a → ℤ) (τ : ZMod a) (i k : Unit) :
    (rankOne O K l e j).mxInv τ i k = Ezpow K l e (-j τ) := by sorry
