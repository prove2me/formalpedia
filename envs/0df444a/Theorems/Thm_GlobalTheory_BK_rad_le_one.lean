-- Prove2me | Theorems.Thm_GlobalTheory_BK_rad_le_one
-- name    : GlobalTheory.BK.rad_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:59.618346+00:00
-- url     : https://prove2.me/theorems/291f2b55-dc31-4707-90c1-d8b673a0d479
-- title:
--   BK: rad le one
-- statement:
--   The BK construction uses the rad le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L370-L371
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L370-L371

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

theorem GlobalTheory.BK.rad_le_one (l : ℕ) [Fact l.Prime] {k : ℝ} (hk : 0 ≤ k) : rad l k ≤ 1 := by sorry
