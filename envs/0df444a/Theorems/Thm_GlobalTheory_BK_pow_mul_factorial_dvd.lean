-- Prove2me | Theorems.Thm_GlobalTheory_BK_pow_mul_factorial_dvd
-- name    : GlobalTheory.BK.pow_mul_factorial_dvd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:29:14.660515+00:00
-- url     : https://prove2.me/theorems/087a9596-c6f7-4120-ba8e-2852b4f9a193
-- title:
--   BK: pow mul factorial dvd
-- statement:
--   The BK construction uses the pow mul factorial dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqMulAddOfIsAdicComplete.lean#L47-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/ExistsEqMulAddOfIsAdicComplete.lean#L47-L57

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

theorem GlobalTheory.BK.pow_mul_factorial_dvd (l k : ℕ) (hl : 0 < l) : l ^ k * k.factorial ∣ (l * k).factorial := by sorry
