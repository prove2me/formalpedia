-- Prove2me | Theorems.Thm_GlobalTheory_BK_norm_coeff_derivative_le
-- name    : GlobalTheory.BK.norm_coeff_derivative_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:21:01.833829+00:00
-- url     : https://prove2.me/theorems/e73247ff-4025-437b-9323-5ea4803a0894
-- title:
--   BK: norm coeff derivative le
-- statement:
--   The BK construction uses the norm coeff derivative le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L397-L401
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/NormPowLeNormFactorial.lean#L397-L401

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

theorem GlobalTheory.BK.norm_coeff_derivative_le (f : K⟦X⟧) (n : ℕ) :
    ‖coeff n (PowerSeries.derivative K f)‖ ≤ ‖coeff (n + 1) f‖ := by sorry
