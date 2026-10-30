-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_all_short_smooth_cubic_neighborhood
-- name    : OAI.CubicFirstMoment.all_short_smooth_cubic_neighborhood
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T03:54:36.763488+00:00
-- url     : https://prove2.me/theorems/d772f3e9-5951-4074-b1aa-79b3f31cd66b
-- title:
--   OAI.CubicFirstMoment.all_short_smooth_cubic_neighborhood: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.all_short_smooth_cubic_neighborhood` of [lean/OAI/NumberTheory/CubicMoment/Estimates/SmoothShortNeighborhoods.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/SmoothShortNeighborhoods.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem all_short_smooth_cubic_neighborhood {δ C : ℝ} (hδ : 0 < δ) (hC : 0 < C) :
--       ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/2 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ,
--         ∀ (F Y N : ℝ) (X : ι → ℝ) (A : ι → EisensteinArithmeticFunction)
--           (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
--           (W : ι → ℝ → ℂ) (t : ι → ℝ) (P : Finset Eisenstein),
--         Y₀ ≤ Y → Y^(1-κ) ≤ N → N ≤ Y^(1+κ) → (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
--         (∀ i, q i ≠ 0) → (∀ i x, ‖W i x‖ ≤ 1) → (∀ i x, 2 < x → W i x = 0) →
--         (∀ i, X i ≤ Y^(1-δ)) → Y/C ≤ ∏ i, X i → (∏ i, X i) ≤ C*Y →
--         (∀ a ∈ P, gramDyad N a) →
--         (∑ a ∈ P, ‖∏ i, primaryShortSmoothSum (A i) a 1 (q i) (η i) (W i) (X i/2) (t i)‖^2) ≤
--           Y^(7/3-ε)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.EisensteinArithmeticFunction` (definitions bundle `OAIQ096A000` of this split); `OAI.CubicFirstMoment.ShortArithmeticFactor` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.gramDyad` (definitions bundle `OAIQ096A005` of this split); `OAI.CubicFirstMoment.primaryShortSmoothSum` (definitions bundle `OAIQ096A010` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.Residues` and `OAI.CubicFirstMoment.modulus` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.first_weighted_tuple_neighborhood` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/SmoothShortNeighborhoods.lean (declaration OAI.CubicFirstMoment.all_short_smooth_cubic_neighborhood)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A010

section

attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem all_short_smooth_cubic_neighborhood {δ C : ℝ} (hδ : 0 < δ) (hC : 0 < C) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/2 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ,
      ∀ (F Y N : ℝ) (X : ι → ℝ) (A : ι → EisensteinArithmeticFunction)
        (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
        (W : ι → ℝ → ℂ) (t : ι → ℝ) (P : Finset Eisenstein),
      Y₀ ≤ Y → Y^(1-κ) ≤ N → N ≤ Y^(1+κ) → (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      (∀ i, q i ≠ 0) → (∀ i x, ‖W i x‖ ≤ 1) → (∀ i x, 2 < x → W i x = 0) →
      (∀ i, X i ≤ Y^(1-δ)) → Y/C ≤ ∏ i, X i → (∏ i, X i) ≤ C*Y →
      (∀ a ∈ P, gramDyad N a) →
      (∑ a ∈ P, ‖∏ i, primaryShortSmoothSum (A i) a 1 (q i) (η i) (W i) (X i/2) (t i)‖^2) ≤
        Y^(7/3-ε) := by
  sorry

end CubicFirstMoment

end

end OAI
end
