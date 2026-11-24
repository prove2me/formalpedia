-- Prove2me | Theorems.Thm_GlobalTheory_ThetaLarge_form_symm
-- name    : GlobalTheory.ThetaLarge.form_symm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:06:46.465728+00:00
-- url     : https://prove2.me/theorems/b094a7d3-93e6-42e3-af5b-519de93fc1b6
-- title:
--   Theta Large: form symm
-- statement:
--   The Theta Large construction uses the form symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsThetaSeriesApplyNeZeroOfLargeForm.lean#L172-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsThetaSeriesApplyNeZeroOfLargeForm.lean#L172-L180

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsThetaSeriesApplyNeZeroOfLargeForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.ThetaLarge
variable {g : ℕ}

theorem GlobalTheory.ThetaLarge.form_symm {M : Matrix (Fin g) (Fin g) ℂ} (hM : M.IsHermitian) (x y : Fin g → ℂ) :
    y ⬝ᵥ M.mulVec (star x) = (starRingEnd ℂ) (x ⬝ᵥ M.mulVec (star y)) := by sorry
