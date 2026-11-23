-- Prove2me | Theorems.Thm_GlobalTheory_Hk_RayCont_norm_integrand_le
-- name    : GlobalTheory.Hk.RayCont.norm_integrand_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:58.029986+00:00
-- url     : https://prove2.me/theorems/9784625d-a51e-423c-9878-f522f9724880
-- title:
--   Ray Cont: norm integrand le
-- statement:
--   The Ray Cont construction uses the norm integrand le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionFamilyContinuationGrowth.lean#L55-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionFamilyContinuationGrowth.lean#L55-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RayCont
open Asymptotics
variable {E : ℝ → ℂ} {C : ℝ}

theorem GlobalTheory.Hk.RayCont.norm_integrand_le (hC : ∀ x, 1 ≤ x → ‖E x‖ ≤ C * Real.sqrt x) (s : ℂ) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioi (1 : ℝ))),
      ‖E t * (t : ℂ) ^ (-s - 1)‖ ≤ C * t ^ (-(s.re + 1 / 2)) := by sorry
