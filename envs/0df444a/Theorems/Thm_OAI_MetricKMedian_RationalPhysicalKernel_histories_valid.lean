-- Prove2me | Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_histories_valid
-- name    : OAI.MetricKMedian.RationalPhysicalKernel.histories_valid
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:36:42.597356+00:00
-- url     : https://prove2.me/theorems/7da50749-7efc-4cfa-b191-66c6246ab467
-- title:
--   OAI.MetricKMedian.RationalPhysicalKernel.histories_valid: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.RationalPhysicalKernel`, with `open Finset PhysicalPotential`):
--
--   ```lean
--   theorem histories_valid (d₀ : F → F → ℚ) (location : F → X) (client : J → X)
--       (hd₀ : ∀ i j, dist (location i) (location j)=(d₀ i j:ℝ))
--       (g β p φ : ℚ) (P : ℕ → ℚ) (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
--       (A : Finset (CopyState.Copy (F := F) Δ)) (S₀ : J → Finset (CopyState.Copy (F := F) Δ))
--       (R : J → ℝ) (T : ℕ) (x : ℕ → ℝ)
--       (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
--       (hP : ∀ t<T, 0<(P t:ℝ)) (hP1 : ∀ t<T, (P t:ℝ)≤1/2)
--       (hA : 1 ≤ mass (g:ℝ) A) (hSA : ∀ j, S₀ j⊆A)
--       (hR : ∀ j, 0≤R j) (hm : ∀ j, mass (g:ℝ) (S₀ j)=1)
--       (hdR : ∀ j i, i∈S₀ j → dist (client j) (location i.1)≤R j)
--       (a : Fin (histories d₀ g β p φ P hp hφ hupper A T).length) :
--       let z := (histories d₀ g β p φ P hp hφ hupper A T).states[a.val];
--       CopyState.Valid (g:ℝ) location client R S₀
--         (z.1.1, replay g β x (fun j f => dist (client j) (location f)) S₀ z)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.CopyState.Copy` and `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ035K003` of this split); `OAI.MetricKMedian.SparseHistories.History` (definitions bundle `OAIQ035K005` of this split); `OAI.MetricKMedian.CopyState.Valid` (definitions bundle `OAIQ035K015` of this split); `OAI.MetricKMedian.RationalPhysicalKernel.Payload`, `OAI.MetricKMedian.RationalPhysicalKernel.State` and `OAI.MetricKMedian.SparseIntegerLaw` (definitions bundle `OAIQ035K017` of this split); `OAI.MetricKMedian.RationalPhysicalKernel.replay` (definitions bundle `OAIQ035K044` of this split); `OAI.MetricKMedian.RationalPhysicalKernel.histories` (definitions bundle `OAIQ035K047` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.RationalPhysicalKernel.histories_completion` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K044
import Definitions.Def_OAIQ035K047

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential
variable {F J X : Type} [LinearOrder F] [Fintype F] [Fintype J] [DecidableEq J]
  [PseudoMetricSpace X] {Δ : ℕ}

omit [Fintype J] [DecidableEq J] in
theorem histories_valid (d₀ : F → F → ℚ) (location : F → X) (client : J → X)
    (hd₀ : ∀ i j, dist (location i) (location j)=(d₀ i j:ℝ))
    (g β p φ : ℚ) (P : ℕ → ℚ) (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (A : Finset (CopyState.Copy (F := F) Δ)) (S₀ : J → Finset (CopyState.Copy (F := F) Δ))
    (R : J → ℝ) (T : ℕ) (x : ℕ → ℝ)
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : ∀ t<T, 0<(P t:ℝ)) (hP1 : ∀ t<T, (P t:ℝ)≤1/2)
    (hA : 1 ≤ mass (g:ℝ) A) (hSA : ∀ j, S₀ j⊆A)
    (hR : ∀ j, 0≤R j) (hm : ∀ j, mass (g:ℝ) (S₀ j)=1)
    (hdR : ∀ j i, i∈S₀ j → dist (client j) (location i.1)≤R j)
    (a : Fin (histories d₀ g β p φ P hp hφ hupper A T).length) :
    let z := (histories d₀ g β p φ P hp hφ hupper A T).states[a.val];
    CopyState.Valid (g:ℝ) location client R S₀
      (z.1.1, replay g β x (fun j f => dist (client j) (location f)) S₀ z) := by
  sorry

end MetricKMedian.RationalPhysicalKernel
end

end OAI
end
