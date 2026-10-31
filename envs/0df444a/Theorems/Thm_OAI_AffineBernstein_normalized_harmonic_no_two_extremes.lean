-- Prove2me | Theorems.Thm_OAI_AffineBernstein_normalized_harmonic_no_two_extremes
-- name    : OAI.AffineBernstein.normalized_harmonic_no_two_extremes
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:10:59.186821+00:00
-- url     : https://prove2.me/theorems/3ae605cf-40b3-41df-94d7-2ce5e09e854b
-- title:
--   OAI.AffineBernstein.normalized_harmonic_no_two_extremes: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.normalized_harmonic_no_two_extremes` of [lean/OAI/Analysis/AffineBernstein/BoundedHarmonic.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/BoundedHarmonic.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`):
--
--   ```lean
--   theorem normalized_harmonic_no_two_extremes {n : ℕ} (hn : 1 ≤ n) {ρ R : ℝ}
--       (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hR : 1 ≤ R) {d : ℝ} (hd : 0 < d) :
--       ∃ ε : ℝ, 0 < ε ∧ ∀ v : Space n → ℝ, BalancedNormalized ρ R v →
--         ∀ F : Space n → ℝ, ContDiff ℝ ∞ F → (∀ x, 0 ≤ F x ∧ F x ≤ d) →
--         (∀ x, inverseHessianTrace v F x = 0) →
--         ∀ a ∈ Metric.ball (0:Space n) (1/64:ℝ), ∀ b ∈ Metric.ball (0:Space n) (1/64:ℝ),
--           ¬(F a ≤ ε ∧ d-F b ≤ ε)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.BalancedNormalized` and `OAI.AffineBernstein.inverseHessianTrace` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.Space` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proof of `OAI.AffineBernstein.balanced_affineMaximal_constant_det` of this split imports it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/BoundedHarmonic.lean (declaration OAI.AffineBernstein.normalized_harmonic_no_two_extremes)

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

section BoundedHarmonic

theorem normalized_harmonic_no_two_extremes {n : ℕ} (hn : 1 ≤ n) {ρ R : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hR : 1 ≤ R) {d : ℝ} (hd : 0 < d) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ v : Space n → ℝ, BalancedNormalized ρ R v →
      ∀ F : Space n → ℝ, ContDiff ℝ ∞ F → (∀ x, 0 ≤ F x ∧ F x ≤ d) →
      (∀ x, inverseHessianTrace v F x = 0) →
      ∀ a ∈ Metric.ball (0:Space n) (1/64:ℝ), ∀ b ∈ Metric.ball (0:Space n) (1/64:ℝ),
        ¬(F a ≤ ε ∧ d-F b ≤ ε) := by
  sorry

end BoundedHarmonic

end
end AffineBernstein
end

end OAI
end
