-- Prove2me | Theorems.Thm_GlobalTheory_BK_rad_nonneg
-- name    : GlobalTheory.BK.rad_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:29.689311+00:00
-- url     : https://prove2.me/theorems/1ca83772-6e0f-43ee-b5f8-f87ea72a51f1
-- title:
--   BK: rad nonneg
-- statement:
--   The BK construction uses the rad nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L158-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L158-L158

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

theorem GlobalTheory.BK.rad_nonneg (l : ℕ) (k : ℝ) : 0 ≤ rad l k := by sorry
