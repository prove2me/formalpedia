-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_WeakLimit_exists_smooth_near
-- name    : GroundTheory.Automorphic.WeakLimit.exists_smooth_near
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:33:46.672546+00:00
-- url     : https://prove2.me/theorems/c05c7f7d-bfb0-4c71-9271-f38d09229409
-- title:
--   Weak Limit: exists smooth near
-- statement:
--   The Weak Limit construction uses the exists smooth near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineLimit.lean#L28-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineLimit.lean#L28-L57

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineLimit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Filter Topology Set
open scoped FourierTransform ContDiff
open GroundTheory.Automorphic.WeakLimit

theorem GroundTheory.Automorphic.WeakLimit.exists_smooth_near (a b : ℝ) {ψ : ℝ → ℂ} (hψ : Continuous ψ) {η : ℝ} (hη : 0 < η) :
    ∃ ψ' : ℝ → ℂ, ContDiff ℝ ∞ ψ' ∧ HasCompactSupport ψ' ∧ ∀ t ∈ Icc a b, ‖ψ t - ψ' t‖ ≤ η := by sorry
