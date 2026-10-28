-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_stationary_product_radial_bound
-- name    : OAI.PlanarFalconer.stationary_product_radial_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:56:10.027224+00:00
-- url     : https://prove2.me/theorems/78705020-fece-4671-a9a1-2d5ad7e7368b
-- title:
--   OAI.PlanarFalconer.stationary_product_radial_bound: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.stationary_product_radial_bound` of [lean/OAI/MeasureTheory/Falconer/Falconer/Angular/StationaryProductKernel.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Angular/StationaryProductKernel.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open Set MeasureTheory`, `open scoped ContDiff`):
--
--   ```lean
--   theorem stationary_product_radial_bound {Ψ : ℝ → ℝ}
--       (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) (n : ℕ) :
--       ∃ H : ℝ, 0 ≤ H ∧ ∀ {f g : ℝ → ℂ}, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
--       ∀ {C E D R d₁ d₂ : ℝ}, 0 ≤ C → 0 ≤ E → 1 ≤ D → 0 < R → 0 < d₁ → 0 < d₂ →
--       D^2 ≤ R*d₁ → D^2 ≤ R*d₂ →
--       (∀ l ≤ 2*n, ∀ t, ‖iteratedDeriv l f t‖ ≤ C*D^l) →
--       (∀ l ≤ 2*n, ∀ t, ‖iteratedDeriv l g t‖ ≤ E*D^l) →
--       ‖R⁻¹ • (∫ r : ℝ, Ψ (r/R) •
--         (fullCircleStationaryExpansion (r*d₁) f n * fullCircleStationaryExpansion (r*d₂) g n))‖ ≤
--         H*C*E*((R*d₁)^(-1/2:ℝ)*(R*d₂)^(-1/2:ℝ))/(1+R*|d₁-d₂|)^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.fullCircleStationaryExpansion` (definitions bundle `OAIQ038F000` of this split).
--
--   **Used by.** The proofs of `OAI.PlanarFalconer.uniform_actual_comparable_shell_rebin` and `OAI.PlanarFalconer.uniform_actual_far_stationary_integrable` of this split import it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Angular/StationaryProductKernel.lean (declaration OAI.PlanarFalconer.stationary_product_radial_bound)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ038F000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem stationary_product_radial_bound {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) (n : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ {f g : ℝ → ℂ}, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
    ∀ {C E D R d₁ d₂ : ℝ}, 0 ≤ C → 0 ≤ E → 1 ≤ D → 0 < R → 0 < d₁ → 0 < d₂ →
    D^2 ≤ R*d₁ → D^2 ≤ R*d₂ →
    (∀ l ≤ 2*n, ∀ t, ‖iteratedDeriv l f t‖ ≤ C*D^l) →
    (∀ l ≤ 2*n, ∀ t, ‖iteratedDeriv l g t‖ ≤ E*D^l) →
    ‖R⁻¹ • (∫ r : ℝ, Ψ (r/R) •
      (fullCircleStationaryExpansion (r*d₁) f n * fullCircleStationaryExpansion (r*d₂) g n))‖ ≤
      H*C*E*((R*d₁)^(-1/2:ℝ)*(R*d₂)^(-1/2:ℝ))/(1+R*|d₁-d₂|)^2 := by
  sorry

end PlanarFalconer

end OAI
end
