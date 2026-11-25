-- Prove2me | Theorems.Thm_GlobalTheory_norm_le_lintegral_ray_iteratedFDeriv
-- name    : GlobalTheory.norm_le_lintegral_ray_iteratedFDeriv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:13:09.464489+00:00
-- url     : https://prove2.me/theorems/8a74dba3-9a33-4356-ba97-f8e6ab0c0eb3
-- title:
--   Global Theory: norm le lintegral ray iterated FDeriv
-- statement:
--   The Global Theory construction uses the norm le lintegral ray iterated FDeriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormLeLintegralRayIteratedFDeriv.lean#L8-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormLeLintegralRayIteratedFDeriv.lean#L8-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormLeLintegralTaylorTailIteratedDerivStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormLeLintegralRayIteratedFDeriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set Module
open scoped ENNReal
open GlobalTheory

theorem GlobalTheory.norm_le_lintegral_ray_iteratedFDeriv
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (G : E → F) (m : ℕ) (x v : E)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hdec : ∀ j ≤ m, Tendsto (fun t : ℝ => iteratedFDeriv ℝ j G (x + t • v)) atTop (𝓝 0)) :
    ENNReal.ofReal ‖G x‖ ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ m / (m.factorial : ℝ) *
      (‖v‖ ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖)) := by sorry
