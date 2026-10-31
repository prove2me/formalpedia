-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_gramDualTerm_dyad_rapidDecay
-- name    : OAI.CubicFirstMoment.gramDualTerm_dyad_rapidDecay
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:00:17.941562+00:00
-- url     : https://prove2.me/theorems/77e0328e-2c35-4e8e-9611-8effb6d1cb8a
-- title:
--   OAI.CubicFirstMoment.gramDualTerm_dyad_rapidDecay: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.gramDualTerm_dyad_rapidDecay` of [lean/OAI/NumberTheory/CubicGram/GramMellin.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicGram/GramMellin.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open scoped BigOperators FourierTransform SchwartzMap ContDiff`, `open Set Filter MeasureTheory Topology`):
--
--   ```lean
--   theorem gramDualTerm_dyad_rapidDecay (W : ℝ → ℂ) (hW : HasCompactSupport W)
--       (hW' : ContDiff ℝ ∞ W) {ε : ℝ} (hε : 0 < ε) (A : ℕ) :
--       ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Eisenstein) (N : ℝ), 1 ≤ 2*N →
--         (∀ b ∈ P, primary b ∧ Squarefree b ∧ N ≤ norm b ∧ norm b ≤ 2*N) →
--         ∀ (a : Eisenstein), primary a → ∀ (Z : ℝ), 0 ≤ Z → ∀ j : ℕ,
--         (1+Z*(2 : ℝ)^j/(27*norm a*N))^(2*A) *
--           (∑ b ∈ P, ‖∑ n ∈ frequencyDyad j, gramDualTerm a b W Z n‖^2) ≤
--           C*((2*N)*(2 : ℝ)^j)^ε*(2 : ℝ)^j*
--             (2*N+(2 : ℝ)^j+((2*N)*(2 : ℝ)^j)^(2/3 : ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.frequencyDyad` (definitions bundle `OAIQ096A005` of this split); `OAI.CubicFirstMoment.gramDualTerm` (definitions bundle `OAIQ096A008` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.norm` and `OAI.CubicFirstMoment.primary` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proofs of `OAI.CubicFirstMoment.all_short_smooth_cubic_neighborhood` and `OAI.CubicFirstMoment.angular_all_short_smooth_cubic_neighborhood` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicGram/GramMellin.lean (declaration OAI.CubicFirstMoment.gramDualTerm_dyad_rapidDecay)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A008

section

attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem gramDualTerm_dyad_rapidDecay (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) {ε : ℝ} (hε : 0 < ε) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Eisenstein) (N : ℝ), 1 ≤ 2*N →
      (∀ b ∈ P, primary b ∧ Squarefree b ∧ N ≤ norm b ∧ norm b ≤ 2*N) →
      ∀ (a : Eisenstein), primary a → ∀ (Z : ℝ), 0 ≤ Z → ∀ j : ℕ,
      (1+Z*(2 : ℝ)^j/(27*norm a*N))^(2*A) *
        (∑ b ∈ P, ‖∑ n ∈ frequencyDyad j, gramDualTerm a b W Z n‖^2) ≤
        C*((2*N)*(2 : ℝ)^j)^ε*(2 : ℝ)^j*
          (2*N+(2 : ℝ)^j+((2*N)*(2 : ℝ)^j)^(2/3 : ℝ)) := by
  sorry

end CubicFirstMoment
end
end

end OAI
end
