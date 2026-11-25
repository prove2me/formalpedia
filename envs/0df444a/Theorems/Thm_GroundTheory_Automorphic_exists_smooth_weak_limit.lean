-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exists_smooth_weak_limit
-- name    : GroundTheory.Automorphic.exists_smooth_weak_limit
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:35:00.724898+00:00
-- url     : https://prove2.me/theorems/8a47c9f6-3228-4de8-ad06-4ea2626282c3
-- title:
--   Automorphic: exists smooth weak limit
-- statement:
--   The Automorphic construction uses the exists smooth weak limit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineLimit.lean#L61-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineLimit.lean#L61-L217

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

theorem GroundTheory.Automorphic.exists_smooth_weak_limit {K : ℕ → ℝ → ℝ} {a b : ℝ} (hKi : ∀ N, Integrable (K N))
    (hK0 : ∀ N t, 0 ≤ K N t) (hK1 : ∀ N, ∫ t, K N t ≤ 1)
    (hKs : ∀ N, Function.support (K N) ⊆ Icc a b)
    (hconv : ∀ ξ : ℝ, ∃ l : ℂ, Tendsto (fun N => 𝓕 (fun t => (K N t : ℂ)) ξ) atTop (𝓝 l))
    (hdecay : ∀ m : ℕ, ∃ C N₀, ∀ N ≥ N₀, ∀ ξ : ℝ,
      ‖𝓕 (fun t => (K N t : ℂ)) ξ‖ ≤ C * (1 + |ξ|) ^ (-(m : ℝ))) :
    ∃ g : ℝ → ℂ, ContDiff ℝ ∞ g ∧ tsupport g ⊆ Icc a b ∧
      ∀ ψ : ℝ → ℂ, Continuous ψ →
        Tendsto (fun N => ∫ t, ψ t * K N t) atTop (𝓝 (∫ t, ψ t * g t)) := by sorry
