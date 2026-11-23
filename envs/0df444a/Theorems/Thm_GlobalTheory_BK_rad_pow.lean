-- Prove2me | Theorems.Thm_GlobalTheory_BK_rad_pow
-- name    : GlobalTheory.BK.rad_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:21:09.830853+00:00
-- url     : https://prove2.me/theorems/978002a4-300a-45d2-8cc3-d2adf1dc80d6
-- title:
--   BK: rad pow
-- statement:
--   The BK construction uses the rad pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L517-L520
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L517-L520

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
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
include l
omit [IsUltrametricDist K]

theorem GlobalTheory.BK.rad_pow (e : ℕ) [NeZero e] : rad l (1 / e) ^ e = ‖(l : K)‖ := by sorry
