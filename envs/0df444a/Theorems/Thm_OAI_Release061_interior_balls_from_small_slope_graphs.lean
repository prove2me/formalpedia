-- Prove2me | Theorems.Thm_OAI_Release061_interior_balls_from_small_slope_graphs
-- name    : OAI.Release061.interior_balls_from_small_slope_graphs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T21:50:40.061978+00:00
-- url     : https://prove2.me/theorems/7f8372dd-0c55-4d49-848a-d9f36ce0001d
-- title:
--   OAI.Release061.interior_balls_from_small_slope_graphs: intermediate lemma from OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Release061.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symmetry of semialgebraic bounded domains with compact quotient (result family 058)*, OpenAI Math Release, September 24, 2026, result family 58, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Release061.interior_balls_from_small_slope_graphs` of [lean/OAI/Analysis/SymmetricDomains/InteriorBallsSmallSlope.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SymmetricDomains/InteriorBallsSmallSlope.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Release061`, with `open Set Metric Complex`, `open scoped Topology`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open scoped Topology ContDiff`, `open Filter`, `open scoped BigOperators Topology ContDiff`, `open Set Filter MeasureTheory`, `open scoped Topology`, `open Set Filter`, `open Set Metric`, `open scoped Topology`, `open Set Filter Metric`, `open scoped Topology`, `open Set Filter`, `open scoped Topology`, `open Set Filter`, `open scoped Topology`, `open Set Filter Metric`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open scoped BigOperators NNReal ENNReal Topology`, `open Set Filter`, `open Set Filter Metric`, `open scoped Topology`):
--
--   ```lean
--   theorem interior_balls_from_small_slope_graphs {k : ℕ} {Ω : Set (Fin k → ℂ)}
--       (hΩ : IsOpen Ω) {ε : ℝ} (hε : 0 < ε) (hCP : Wiener.DiscContinuityWithin k Ω ε)
--       {φ : (Fin k → ℝ) → Fin k → ℝ} (hφ : AnalyticAt ℝ φ 0) (hφ0 : φ 0 = 0)
--       (hdφ : ‖fderiv ℝ φ 0‖ < 1/2)
--       {G : (Fin k → ℝ) × ℝ → Fin k → ℂ} (hG : AnalyticAt ℝ G 0)
--       (hG0 : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ),
--         G (x,0) = fun i => (x i : ℂ)+Complex.I*(φ x i : ℂ))
--       (hGΩ : ∀ᶠ q in 𝓝 (0 : (Fin k → ℝ) × ℝ), 0 < q.2 → G q ∈ Ω) :
--       ∃ c C t₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < t₀ ∧ ∀ t, 0 < t → t < t₀ →
--         ∃ a : Fin k → ℂ, ‖a‖ ≤ C*t ∧ ball a (c*t) ⊆ Ω
--   ```
--
--   **Definitions.** The statement is written with `OAI.Release061.Wiener.DiscContinuityWithin` (definitions bundle `OAIQ025S001` of this split).
--
--   **Used by.** The proof of `OAI.Release061.original_supported_hermitian_model` of this split imports it.
-- source:
--   OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 58; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symmetry-of-semialgebraic-bounded-domains-with-compact-quotient-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/SymmetricDomains/InteriorBallsSmallSlope.lean (declaration OAI.Release061.interior_balls_from_small_slope_graphs)

import Mathlib
import Definitions.Def_OAIQ025S001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric
open scoped Topology

theorem interior_balls_from_small_slope_graphs {k : ℕ} {Ω : Set (Fin k → ℂ)}
    (hΩ : IsOpen Ω) {ε : ℝ} (hε : 0 < ε) (hCP : Wiener.DiscContinuityWithin k Ω ε)
    {φ : (Fin k → ℝ) → Fin k → ℝ} (hφ : AnalyticAt ℝ φ 0) (hφ0 : φ 0 = 0)
    (hdφ : ‖fderiv ℝ φ 0‖ < 1/2)
    {G : (Fin k → ℝ) × ℝ → Fin k → ℂ} (hG : AnalyticAt ℝ G 0)
    (hG0 : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ),
      G (x,0) = fun i => (x i : ℂ)+Complex.I*(φ x i : ℂ))
    (hGΩ : ∀ᶠ q in 𝓝 (0 : (Fin k → ℝ) × ℝ), 0 < q.2 → G q ∈ Ω) :
    ∃ c C t₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < t₀ ∧ ∀ t, 0 < t → t < t₀ →
      ∃ a : Fin k → ℂ, ‖a‖ ≤ C*t ∧ ball a (c*t) ⊆ Ω := by
  sorry

end Release061

end

end OAI
end
