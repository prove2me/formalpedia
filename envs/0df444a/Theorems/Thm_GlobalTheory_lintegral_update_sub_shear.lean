-- Prove2me | Theorems.Thm_GlobalTheory_lintegral_update_sub_shear
-- name    : GlobalTheory.lintegral_update_sub_shear
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:57:01.023423+00:00
-- url     : https://prove2.me/theorems/c3f9feff-b765-4065-9982-b645d87f6356
-- title:
--   Global Theory: lintegral update sub shear
-- statement:
--   The Global Theory construction uses the lintegral update sub shear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralUpdateSubShear.lean#L8-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralUpdateSubShear.lean#L8-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralUpdateSubShear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
open GlobalTheory

theorem GlobalTheory.lintegral_update_sub_shear {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι)
    (g : (ι → ℂ) → ℂ) (hg : Measurable g)
    (hgi : ∀ w v : ι → ℂ, (∀ j, j ≠ i → w j = v j) → g w = g v)
    (F : (ι → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ w, F (Function.update w i (w i - g w)) = ∫⁻ w, F w := by sorry
