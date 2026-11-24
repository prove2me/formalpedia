-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GL2Classical_integral_periodic_eq_of_im
-- name    : GroundTheory.Automorphic.GL2Classical.integral_periodic_eq_of_im
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:29:48.506988+00:00
-- url     : https://prove2.me/theorems/36f404f1-89ca-486e-aa94-a09cbe88dccf
-- title:
--   GL2 Classical: integral periodic eq of im
-- statement:
--   The GL2 Classical construction uses the integral periodic eq of im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2Classical/Periodic.lean#L13-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2Classical/Periodic.lean#L13-L45

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

theorem GroundTheory.Automorphic.GL2Classical.integral_periodic_eq_of_im {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G {w | 0 < w.im}) {T : ℝ}
    (hper : ∀ w : ℂ, 0 < w.im → G (w + T) = G w) (x₀ : ℝ) {y₁ y₂ : ℝ} (hy₁ : 0 < y₁)
    (hy₂ : 0 < y₂) :
    ∫ x in x₀..x₀ + T, G (x + y₁ * I) = ∫ x in x₀..x₀ + T, G (x + y₂ * I) := by sorry
