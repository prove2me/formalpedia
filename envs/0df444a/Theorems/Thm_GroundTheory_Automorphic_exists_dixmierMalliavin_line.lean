-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exists_dixmierMalliavin_line
-- name    : GroundTheory.Automorphic.exists_dixmierMalliavin_line
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:58:10.927435+00:00
-- url     : https://prove2.me/theorems/1f1a6643-8ffe-4c02-a18f-edd400c35cb8
-- title:
--   Automorphic: exists dixmier Malliavin line
-- statement:
--   The Automorphic construction uses the exists dixmier Malliavin line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLine.lean#L297-L391
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLine.lean#L297-L391

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineLimit
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise FourierTransform
set_option linter.unusedSectionVars false
noncomputable section
open LineKernel

theorem GroundTheory.Automorphic.exists_dixmierMalliavin_line (M : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (c : ℕ → ℝ) (g h : ℝ → ℂ), ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ h ∧
      tsupport g ⊆ Set.Icc (-ε) ε ∧ tsupport h ⊆ Set.Icc (-ε) ε ∧
      Summable (fun p => |c p| * M p) ∧
      ∀ F : ℝ → ℂ, ContDiff ℝ ∞ F → (∀ p, ∀ t ∈ Set.Icc (-ε) ε, ‖iteratedDeriv p F t‖ ≤ M p) →
        F 0 = (∑' p, (c p : ℂ) * ∫ t, iteratedDeriv p F t * g t) + ∫ t, F t * h t := by sorry
