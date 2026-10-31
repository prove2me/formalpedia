-- Prove2me | Theorems.Thm_OAI_AffineBernstein_normalized_supersolution_high_set_small
-- name    : OAI.AffineBernstein.normalized_supersolution_high_set_small
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:11:21.999069+00:00
-- url     : https://prove2.me/theorems/a5f72c22-75e7-478c-b9a0-bfb93db135da
-- title:
--   OAI.AffineBernstein.normalized_supersolution_high_set_small: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.normalized_supersolution_high_set_small` of [lean/OAI/Analysis/AffineBernstein/SupersolutionHighSet.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/SupersolutionHighSet.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`):
--
--   ```lean
--   theorem normalized_supersolution_high_set_small {n : ℕ} (hn : 1 ≤ n) {ρ R : ℝ}
--       (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hR : 1 ≤ R) {η β : ℝ} (hη : 0 < η) (hβ : 0 < β) :
--       ∃ ε : ℝ, 0 < ε ∧ ∀ v : Space n → ℝ, BalancedNormalized ρ R v →
--         ∀ s : Space n → ℝ, ContDiff ℝ ∞ s → (∀ x, 0 ≤ s x) →
--         (∀ x, inverseHessianTrace v s x ≤ 0) → ∀ a ∈ Metric.ball (0:Space n) (1/64:ℝ),
--         s a ≤ ε → (volume {x | x ∈ Metric.closedBall (0:Space n) (1/16:ℝ) ∧ η ≤ s x}).toReal < β
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.BalancedNormalized` and `OAI.AffineBernstein.inverseHessianTrace` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.Space` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proof of `OAI.AffineBernstein.balanced_constant_hessian` of this split imports it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/SupersolutionHighSet.lean (declaration OAI.AffineBernstein.normalized_supersolution_high_set_small)

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section SupersolutionHighSet

theorem normalized_supersolution_high_set_small {n : ℕ} (hn : 1 ≤ n) {ρ R : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hR : 1 ≤ R) {η β : ℝ} (hη : 0 < η) (hβ : 0 < β) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ v : Space n → ℝ, BalancedNormalized ρ R v →
      ∀ s : Space n → ℝ, ContDiff ℝ ∞ s → (∀ x, 0 ≤ s x) →
      (∀ x, inverseHessianTrace v s x ≤ 0) → ∀ a ∈ Metric.ball (0:Space n) (1/64:ℝ),
      s a ≤ ε → (volume {x | x ∈ Metric.closedBall (0:Space n) (1/16:ℝ) ∧ η ≤ s x}).toReal < β := by
  sorry

end SupersolutionHighSet

end
end AffineBernstein
end

end OAI
end
