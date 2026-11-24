-- Prove2me | Theorems.Thm_GlobalTheory_BK_wS_anti
-- name    : GlobalTheory.BK.wS_anti
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:00:20.18678+00:00
-- url     : https://prove2.me/theorems/2795197e-3960-423c-839b-146e724d94bf
-- title:
--   BK: w S anti
-- statement:
--   The BK construction uses the w S anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L75-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L75-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial
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
open PowerSeries Filter Topology
variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem GlobalTheory.BK.wS_anti (e : ℕ) {i j : ℕ} (h : i ≤ j) : wS K e j ≤ wS K e i := by sorry
