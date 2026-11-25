-- Prove2me | Theorems.Thm_Kyprianou_Ch04_uniformBoundedMultiplierV1
-- name    : Kyprianou.Ch04.uniformBoundedMultiplierV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:25:29.695587+00:00
-- url     : https://prove2.me/theorems/d452ad12-2015-598f-ad4d-3619e2dcf502
-- title:
--   Uniform convergence under fixed bounded multiplication
-- statement:
--   Uniform convergence of real-valued functions on a set is preserved by multiplication by a fixed bounded function.
-- source:
--   Supporting integral limit for Kyprianou (2006), Chapter 4, Exercise 4.2.

import Mathlib
open Filter Set
open scoped Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.uniformBoundedMultiplierV1 {I : Type} [Preorder I] [Nonempty I] (F : I → ℝ → ℝ)
    (g h : ℝ → ℝ) (s : Set ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hb : ∀ u ∈ s, |h u| ≤ M)
    (hF : TendstoUniformlyOn F g atTop s) :
    TendstoUniformlyOn (fun i u => F i u * h u)
      (fun u => g u * h u) atTop s := by
  sorry
