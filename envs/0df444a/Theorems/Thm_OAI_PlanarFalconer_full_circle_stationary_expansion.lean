-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_full_circle_stationary_expansion
-- name    : OAI.PlanarFalconer.full_circle_stationary_expansion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:54:43.519808+00:00
-- url     : https://prove2.me/theorems/85623c28-8f9b-4a44-87cb-3862b60eaad9
-- title:
--   OAI.PlanarFalconer.full_circle_stationary_expansion: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.full_circle_stationary_expansion` of [lean/OAI/MeasureTheory/Falconer/Falconer/Angular/FullCircleStationaryExpansion.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Angular/FullCircleStationaryExpansion.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open MeasureTheory`, `open scoped ContDiff ComplexConjugate`):
--
--   ```lean
--    theorem full_circle_stationary_expansion (n M : ℕ) :
--       ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f →
--       Function.Periodic f (2*Real.pi) → ∀ {Λ C D : ℝ}, 0 < Λ → 0 ≤ C → 1 ≤ D →
--       (∀ k ≤ max (2*(n+1)+2) M, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
--       ‖(∫ θ in (-Real.pi)..Real.pi, cosineOscillator Λ θ*f θ) - fullCircleStationaryExpansion Λ f n‖ ≤
--         ((Real.pi/(Λ/2))^(1/2:ℝ) * ((Real.pi^2/(Λ/2))^(n+1)/(n.factorial:ℝ))) *
--           (A*C*D^(2*(n+1)+2)) + B*C*D^M/Λ^M
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.fullCircleStationaryExpansion` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.cosineOscillator` (definitions bundle `OAIQ038F001` of this split).
--
--   **Used by.** The proofs of `OAI.PlanarFalconer.rotated_inverse_circle_power`, `OAI.PlanarFalconer.uniform_actual_far_radial_error` and `OAI.PlanarFalconer.uniform_actual_noncomparable_radial_either` of this split import it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Angular/FullCircleStationaryExpansion.lean (declaration OAI.PlanarFalconer.full_circle_stationary_expansion)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ038F000
import Definitions.Def_OAIQ038F001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff ComplexConjugate

 theorem full_circle_stationary_expansion (n M : ℕ) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f →
    Function.Periodic f (2*Real.pi) → ∀ {Λ C D : ℝ}, 0 < Λ → 0 ≤ C → 1 ≤ D →
    (∀ k ≤ max (2*(n+1)+2) M, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖(∫ θ in (-Real.pi)..Real.pi, cosineOscillator Λ θ*f θ) - fullCircleStationaryExpansion Λ f n‖ ≤
      ((Real.pi/(Λ/2))^(1/2:ℝ) * ((Real.pi^2/(Λ/2))^(n+1)/(n.factorial:ℝ))) *
        (A*C*D^(2*(n+1)+2)) + B*C*D^M/Λ^M := by
  sorry

end PlanarFalconer

end OAI
end
