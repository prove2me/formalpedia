-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_PhaseGeometry_choose_three_avoiding
-- name    : OAI.ClosedSurfaceR4.PhaseGeometry.choose_three_avoiding
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T19:53:28.497195+00:00
-- url     : https://prove2.me/theorems/960f077b-6c45-4f18-94ae-0e1bcd5c0e73
-- title:
--   OAI.ClosedSurfaceR4.PhaseGeometry.choose_three_avoiding: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.PhaseGeometry.choose_three_avoiding` of [lean/OAI/Geometry/Immersion/ClosedSurface/GoodDirections.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/Immersion/ClosedSurface/GoodDirections.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.PhaseGeometry`, with `open Set Complex Bundle Manifold`, `open scoped ContDiff Matrix Topology Manifold BigOperators`, `open Set Polynomial`):
--
--   ```lean
--   lemma choose_three_avoiding {T : Set ℝ} (hT : T.Finite)
--       {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ} (h₀ : a₀ < b₀) (h₁ : a₁ < b₁) (h₂ : a₂ < b₂) :
--       ∃ t₀ ∈ Ioo a₀ b₀, ∃ t₁ ∈ Ioo a₁ b₁, ∃ t₂ ∈ Ioo a₂ b₂,
--         t₀ ∉ T ∧ t₁ ∉ T ∧ t₂ ∉ T ∧ (t₀ + 2*t₁)/3 ∉ T ∧ 2*t₁-t₀ ∉ T ∧
--         (t₀ + 4*t₂)/5 ∉ T ∧ (4*t₂-t₀)/3 ∉ T ∧ (t₁ + 2*t₂)/3 ∉ T ∧ 2*t₂-t₁ ∉ T
--   ```
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.PhaseGeometry.positive_good_phase_data` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/Immersion/ClosedSurface/GoodDirections.lean (declaration OAI.ClosedSurfaceR4.PhaseGeometry.choose_three_avoiding)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open Set Polynomial

lemma choose_three_avoiding {T : Set ℝ} (hT : T.Finite)
    {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ} (h₀ : a₀ < b₀) (h₁ : a₁ < b₁) (h₂ : a₂ < b₂) :
    ∃ t₀ ∈ Ioo a₀ b₀, ∃ t₁ ∈ Ioo a₁ b₁, ∃ t₂ ∈ Ioo a₂ b₂,
      t₀ ∉ T ∧ t₁ ∉ T ∧ t₂ ∉ T ∧ (t₀ + 2*t₁)/3 ∉ T ∧ 2*t₁-t₀ ∉ T ∧
      (t₀ + 4*t₂)/5 ∉ T ∧ (4*t₂-t₀)/3 ∉ T ∧ (t₁ + 2*t₂)/3 ∉ T ∧ 2*t₂-t₁ ∉ T := by
  sorry

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end
