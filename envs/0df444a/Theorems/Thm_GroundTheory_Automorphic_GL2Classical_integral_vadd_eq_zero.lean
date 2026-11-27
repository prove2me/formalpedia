-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GL2Classical_integral_vadd_eq_zero
-- name    : GroundTheory.Automorphic.GL2Classical.integral_vadd_eq_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:52:51.077871+00:00
-- url     : https://prove2.me/theorems/c6861eb3-846f-4488-9629-da818a4f0fc8
-- title:
--   GL2 Classical: integral vadd eq zero
-- statement:
--   The GL2 Classical construction uses the integral vadd eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2Classical/Periodic.lean#L47-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2Classical/Periodic.lean#L47-L102

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2Classical_Periodic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory intervalIntegral Filter Topology Set
open UpperHalfPlane hiding I I_re I_im
open scoped Manifold Interval
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.GL2Classical

theorem GroundTheory.Automorphic.GL2Classical.integral_vadd_eq_zero {F : ℍ → ℂ} (hF : MDiff F) {T : ℝ} (hT : 0 < T)
    (hper : ∀ z : ℍ, F (T +ᵥ z) = F z) (hzero : IsZeroAtImInfty F) (z : ℍ) :
    ∫ t in (0 : ℝ)..T, F (t +ᵥ z) = 0 := by sorry
