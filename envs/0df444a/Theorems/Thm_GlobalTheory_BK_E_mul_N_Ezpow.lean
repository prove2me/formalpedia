-- Prove2me | Theorems.Thm_GlobalTheory_BK_E_mul_N_Ezpow
-- name    : GlobalTheory.BK.E_mul_N_Ezpow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:31:30.066918+00:00
-- url     : https://prove2.me/theorems/aedc8e6b-6d4f-44f1-a176-c24ebb7f1f96
-- title:
--   BK: E mul N Ezpow
-- statement:
--   The BK construction uses the E mul N Ezpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqMulAddOfIsAdicComplete.lean#L88-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqMulAddOfIsAdicComplete.lean#L88-L110

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
omit [IsUltrametricDist K]

theorem GlobalTheory.BK.E_mul_N_Ezpow (j : ℤ) :
    E K l e * N K (Ezpow K l e j) = (j : K⟦X⟧) * N K (E K l e) * Ezpow K l e j := by sorry
