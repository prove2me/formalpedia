-- Prove2me | Theorems.Thm_GlobalTheory_BK_rad_lt_one
-- name    : GlobalTheory.BK.rad_lt_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:00:20.668802+00:00
-- url     : https://prove2.me/theorems/e0c8786f-e21f-4101-b925-6b0bb7c1f316
-- title:
--   BK: rad lt one
-- statement:
--   The BK construction uses the rad lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L373-L374
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L373-L374

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
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K]
variable {O K}

theorem GlobalTheory.BK.rad_lt_one (l : ℕ) [Fact l.Prime] {k : ℝ} (hk : 0 < k) : rad l k < 1 := by sorry
