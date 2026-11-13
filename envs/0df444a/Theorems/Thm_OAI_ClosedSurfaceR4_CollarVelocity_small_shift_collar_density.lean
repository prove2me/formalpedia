-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_CollarVelocity_small_shift_collar_density
-- name    : OAI.ClosedSurfaceR4.CollarVelocity.small_shift_collar_density
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T09:37:50.556728+00:00
-- url     : https://prove2.me/theorems/bf4a3c89-652a-4f92-b835-030b19070b76
-- title:
--   OAI.ClosedSurfaceR4.CollarVelocity.small_shift_collar_density: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.CollarVelocity.small_shift_collar_density` of [lean/OAI/Geometry/SurfaceImmersion/Whitney/ShiftedCollarDensity.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Whitney/ShiftedCollarDensity.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.CollarVelocity`, with `open Set`, `open scoped ContDiff`):
--
--   ```lean
--   theorem small_shift_collar_density {a A s : B → ℝ} {c : B → LoopDensity.Plane}
--       (ha : ContDiff ℝ ∞ a) (hA : ContDiff ℝ ∞ A)
--       (hs : ContDiff ℝ ∞ s) (hc : ContDiff ℝ ∞ c)
--       {U C K : Set B} (hU : IsOpen U) (hC : IsClosed C) (hCU : C ⊆ U) (hK : IsCompact K)
--       (hcollar : ∀ b ∈ U, s b = 0 ∧ c b = ![(1 - a b ^ 2 / 2) / (1 + a b ^ 2 / 2), 0])
--       (hrest : ∀ b ∈ K \ U,
--         (0 < a b ∧ 2 * Real.arctan (a b) ≤ A b ∧ s b ∈ Icc (0 : ℝ) 1 ∧
--           c b = ![(1 - a b ^ 2 / 2) / (1 + a b ^ 2 / 2), 0]) ∨
--         (s b = 1 ∧ Real.pi < A b ∧ c b 0 ^ 2 + c b 1 ^ 2 < 1)) :
--       ∃ ε : ℝ, 0 < ε ∧ ∀ h : B → ℝ, ContDiff ℝ ∞ h →
--         (∀ b, |h b| < ε) → (∀ b ∈ U, h b = 0) →
--         ∃ V : Set B, IsOpen V ∧ K ⊆ V ∧ ∃ ρ : B × ℝ → ℝ,
--           ContDiffOn ℝ ∞ ρ (V ×ˢ univ) ∧
--           (∀ b ∈ V, ∀ t, 0 < ρ (b, t)) ∧
--           (∀ b, Function.Periodic (fun t => ρ (b, t)) 1) ∧
--           (∀ b ∈ V, (∫ t in 0..1, ρ (b, t) •
--             LoopDensity.augment (blendedPath (a b) (A b) (s b) (h b) t)) =
--               LoopDensity.augment (c b)) ∧
--           ∀ b ∈ V ∩ C, ∀ t, ρ (b, t) = unitDensity (a b) t
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.CollarVelocity.blendedPath`, `OAI.ClosedSurfaceR4.CollarVelocity.unitDensity` and `OAI.ClosedSurfaceR4.LoopDensity.Plane` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.LoopDensity.Moments` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.LoopDensity.augment` (definitions bundle `OAIQ249SI005` of this split).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.constructed_surface_collar_family` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Whitney/ShiftedCollarDensity.lean (declaration OAI.ClosedSurfaceR4.CollarVelocity.small_shift_collar_density)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Definitions.Def_OAIQ249SI005

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]

theorem small_shift_collar_density {a A s : B → ℝ} {c : B → LoopDensity.Plane}
    (ha : ContDiff ℝ ∞ a) (hA : ContDiff ℝ ∞ A)
    (hs : ContDiff ℝ ∞ s) (hc : ContDiff ℝ ∞ c)
    {U C K : Set B} (hU : IsOpen U) (hC : IsClosed C) (hCU : C ⊆ U) (hK : IsCompact K)
    (hcollar : ∀ b ∈ U, s b = 0 ∧ c b = ![(1 - a b ^ 2 / 2) / (1 + a b ^ 2 / 2), 0])
    (hrest : ∀ b ∈ K \ U,
      (0 < a b ∧ 2 * Real.arctan (a b) ≤ A b ∧ s b ∈ Icc (0 : ℝ) 1 ∧
        c b = ![(1 - a b ^ 2 / 2) / (1 + a b ^ 2 / 2), 0]) ∨
      (s b = 1 ∧ Real.pi < A b ∧ c b 0 ^ 2 + c b 1 ^ 2 < 1)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h : B → ℝ, ContDiff ℝ ∞ h →
      (∀ b, |h b| < ε) → (∀ b ∈ U, h b = 0) →
      ∃ V : Set B, IsOpen V ∧ K ⊆ V ∧ ∃ ρ : B × ℝ → ℝ,
        ContDiffOn ℝ ∞ ρ (V ×ˢ univ) ∧
        (∀ b ∈ V, ∀ t, 0 < ρ (b, t)) ∧
        (∀ b, Function.Periodic (fun t => ρ (b, t)) 1) ∧
        (∀ b ∈ V, (∫ t in 0..1, ρ (b, t) •
          LoopDensity.augment (blendedPath (a b) (A b) (s b) (h b) t)) =
            LoopDensity.augment (c b)) ∧
        ∀ b ∈ V ∩ C, ∀ t, ρ (b, t) = unitDensity (a b) t := by
  sorry

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end
