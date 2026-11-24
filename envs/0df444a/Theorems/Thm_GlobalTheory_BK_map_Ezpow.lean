-- Prove2me | Theorems.Thm_GlobalTheory_BK_map_Ezpow
-- name    : GlobalTheory.BK.map_Ezpow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:31:14.575259+00:00
-- url     : https://prove2.me/theorems/9ffde4dd-a6b1-4798-b20a-46f9faffd970
-- title:
--   BK: map Ezpow
-- statement:
--   The BK construction uses the map Ezpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqMulAddOfIsAdicComplete.lean#L113-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqMulAddOfIsAdicComplete.lean#L113-L118

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

theorem GlobalTheory.BK.map_Ezpow (f : K⟦X⟧ →+* K⟦X⟧) (hf : f (E K l e) = E K l e) (j : ℤ) :
    f (Ezpow K l e j) = Ezpow K l e j := by sorry
