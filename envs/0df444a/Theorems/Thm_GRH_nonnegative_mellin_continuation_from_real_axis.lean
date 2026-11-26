-- Prove2me | Theorems.Thm_GRH_nonnegative_mellin_continuation_from_real_axis
-- name    : GRH.nonnegative_mellin_continuation_from_real_axis
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T20:55:30.445045+00:00
-- url     : https://prove2.me/theorems/00fa4c74-6c25-5463-ab73-39038b288c8c
-- title:
--   Holomorphic convergence of a nonnegative Mellin transform from continuation along the real axis
-- statement:
--   For a nonnegative measurable function on x greater than one, suppose its Mellin integral converges for real exponents above c. If the transform agrees there on the complex half-plane with a holomorphic function on an open neighborhood of that half-plane and of the real ray above θ, then the integral defines a holomorphic function on the whole half-plane Re s greater than θ.
-- source:
--   Arithmetic reduction of the exact centered progression estimate. https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 The positive Mellin-transform argument is adapted, with attribution and license in the Lean source, from pitimespi. https://prove2.me/submissions/371c6c95-d927-4bbe-822c-d3f6df8f83e7

import Definitions.Def_GRH_OneSidedMoebius

open MeasureTheory Set GRH.OneSidedMoebius

theorem GRH.nonnegative_mellin_continuation_from_real_axis (A : ℝ → ℝ) (hA : Measurable A) (h0 : ∀ x, 1 < x → 0 ≤ A x)
    {θ c : ℝ} (hc : ∀ σ, c < σ → IntegrableOn (fun x : ℝ => A x * x ^ (-σ-1)) (Ioi 1))
    {G : ℂ → ℂ} {U : Set ℂ} (ho : IsOpen U) (hG : DifferentiableOn ℂ G U)
    (hu : ∀ s : ℂ, c < s.re → s ∈ U) (hr : ∀ t : ℝ, θ < t → (t : ℂ) ∈ U)
    (he : ∀ s : ℂ, c < s.re → transform A s = G s) :
    DifferentiableOn ℂ (transform A) {s : ℂ | θ < s.re} := by sorry
