-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_bounded_cubic_moment
-- name    : OAI.CubicFirstMoment.bounded_cubic_moment
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T03:30:32.351107+00:00
-- url     : https://prove2.me/theorems/e2e15784-c4ec-4d72-8dfd-6bfbe49b786d
-- title:
--   OAI.CubicFirstMoment.bounded_cubic_moment: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.bounded_cubic_moment` of [lean/OAI/NumberTheory/CubicMoment/Estimates/SharpPrimaryMoments.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/SharpPrimaryMoments.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem bounded_cubic_moment {ε : ℝ} (hε : 0 < ε) :
--       ∃ C : ℝ, 0 < C ∧ ∀ (P H : Finset Eisenstein) (N Y D : ℝ),
--         1 ≤ N → 1 ≤ Y → 0 ≤ D →
--         (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N) →
--         (∀ n ∈ H, n ≠ 0 ∧ norm n ≤ Y) → ∀ v : Eisenstein → ℂ,
--         (∀ n ∈ H, ‖v n‖ ≤ D) →
--         (∑ a ∈ P, ‖∑ n ∈ H, v n*cubicSymbol a n‖^2) ≤
--           C*(N*Y)^ε*Y*(N+Y+(N*Y)^(2/3:ℝ))*D^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.cubicSymbol` (definitions bundle `OAIQ096A000` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.norm` and `OAI.CubicFirstMoment.primary` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proofs of `OAI.CubicFirstMoment.all_short_smooth_cubic_neighborhood`, `OAI.CubicFirstMoment.angular_all_short_smooth_cubic_neighborhood`, `OAI.CubicFirstMoment.full_smooth_angular_twisted_primitive_cubic_bound` and `OAI.CubicFirstMoment.full_smooth_twisted_primitive_cubic_bound` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/SharpPrimaryMoments.lean (declaration OAI.CubicFirstMoment.bounded_cubic_moment)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem bounded_cubic_moment {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P H : Finset Eisenstein) (N Y D : ℝ),
      1 ≤ N → 1 ≤ Y → 0 ≤ D →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ n ∈ H, n ≠ 0 ∧ norm n ≤ Y) → ∀ v : Eisenstein → ℂ,
      (∀ n ∈ H, ‖v n‖ ≤ D) →
      (∑ a ∈ P, ‖∑ n ∈ H, v n*cubicSymbol a n‖^2) ≤
        C*(N*Y)^ε*Y*(N+Y+(N*Y)^(2/3:ℝ))*D^2 := by
  sorry

end CubicFirstMoment

end

end OAI
end
