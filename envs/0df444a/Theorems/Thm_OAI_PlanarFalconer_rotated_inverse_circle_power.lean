-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_rotated_inverse_circle_power
-- name    : OAI.PlanarFalconer.rotated_inverse_circle_power
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T09:01:02.39357+00:00
-- url     : https://prove2.me/theorems/f7deb025-f6b5-4e6b-bc00-e394c8caaf38
-- title:
--   OAI.PlanarFalconer.rotated_inverse_circle_power: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.rotated_inverse_circle_power` of [lean/OAI/MeasureTheory/Falconer/Falconer/Angular/RotatedInverseCircle.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Angular/RotatedInverseCircle.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open MeasureTheory`, `open scoped ContDiff Topology`):
--
--   ```lean
--   theorem rotated_inverse_circle_power {c sig T : ℝ} (hc : 0 < c) (hsig : 0 < sig) :
--       ∃ n : ℕ, ∀ P C : ℝ, 0 ≤ P → 0 ≤ C → ∃ N₀ : ℕ, ∀ N ≥ N₀,
--       ∀ {ψ f : ℝ → ℂ}, ContDiff ℝ ∞ ψ → ContDiff ℝ ∞ f →
--       Function.Periodic ψ (2*Real.pi) → Function.Periodic f (2*Real.pi) →
--       ∀ θ₀ : ℝ, ψ =ᶠ[𝓝 θ₀] (fun _ => 1) → ψ =ᶠ[𝓝 (θ₀+Real.pi)] (fun _ => 0) →
--       ∀ {D Λ : ℝ}, 1 ≤ D → ((2:ℝ)^N)^(c*sig) ≤ Λ →
--       D ≤ ((2:ℝ)^N)^(1+sig) → D^2/Λ ≤ ((2:ℝ)^N)^(-c*sig) →
--       (∀ k ≤ 4*(n+1)+2, ∀ x, ‖iteratedDeriv k ψ x‖ ≤ P) →
--       (∀ k ≤ 4*(n+1)+2, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
--       ‖Complex.exp (Complex.I*(Λ:ℂ))*f θ₀ - rotatedInverseCircleIntegral n Λ θ₀ ψ f‖ ≤
--         ((2:ℝ)^N)^(-T)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.rotatedInverseCircleIntegral` (definitions bundle `OAIQ038F002` of this split).
--
--   **Used by.** The proofs of `OAI.PlanarFalconer.PositiveDistanceData.uniform_weighted_high_shell_inverse` and `OAI.PlanarFalconer.uniform_root_weighted_inverse` of this split import it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Angular/RotatedInverseCircle.lean (declaration OAI.PlanarFalconer.rotated_inverse_circle_power)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ038F002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff Topology

theorem rotated_inverse_circle_power {c sig T : ℝ} (hc : 0 < c) (hsig : 0 < sig) :
    ∃ n : ℕ, ∀ P C : ℝ, 0 ≤ P → 0 ≤ C → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ψ f : ℝ → ℂ}, ContDiff ℝ ∞ ψ → ContDiff ℝ ∞ f →
    Function.Periodic ψ (2*Real.pi) → Function.Periodic f (2*Real.pi) →
    ∀ θ₀ : ℝ, ψ =ᶠ[𝓝 θ₀] (fun _ => 1) → ψ =ᶠ[𝓝 (θ₀+Real.pi)] (fun _ => 0) →
    ∀ {D Λ : ℝ}, 1 ≤ D → ((2:ℝ)^N)^(c*sig) ≤ Λ →
    D ≤ ((2:ℝ)^N)^(1+sig) → D^2/Λ ≤ ((2:ℝ)^N)^(-c*sig) →
    (∀ k ≤ 4*(n+1)+2, ∀ x, ‖iteratedDeriv k ψ x‖ ≤ P) →
    (∀ k ≤ 4*(n+1)+2, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖Complex.exp (Complex.I*(Λ:ℂ))*f θ₀ - rotatedInverseCircleIntegral n Λ θ₀ ψ f‖ ≤
      ((2:ℝ)^N)^(-T) := by
  sorry

end PlanarFalconer

end OAI
end
