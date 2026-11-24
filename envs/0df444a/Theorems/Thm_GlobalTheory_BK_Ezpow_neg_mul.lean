-- Prove2me | Theorems.Thm_GlobalTheory_BK_Ezpow_neg_mul
-- name    : GlobalTheory.BK.Ezpow_neg_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:31:14.930847+00:00
-- url     : https://prove2.me/theorems/14196ab3-9dc5-45ee-a5fa-760995bc691b
-- title:
--   BK: Ezpow neg mul
-- statement:
--   The BK construction uses the Ezpow neg mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqMulAddOfIsAdicComplete.lean#L121-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqMulAddOfIsAdicComplete.lean#L121-L123

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

theorem GlobalTheory.BK.Ezpow_neg_mul (j : ℤ) : Ezpow K l e (-j) * Ezpow K l e j = 1 := by sorry
