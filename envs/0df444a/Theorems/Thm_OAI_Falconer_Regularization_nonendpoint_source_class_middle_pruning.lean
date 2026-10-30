-- Prove2me | Theorems.Thm_OAI_Falconer_Regularization_nonendpoint_source_class_middle_pruning
-- name    : OAI.Falconer.Regularization.nonendpoint_source_class_middle_pruning
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T21:43:22.510377+00:00
-- url     : https://prove2.me/theorems/bcfb66a9-1f28-4838-8838-bb0037910cbd
-- title:
--   OAI.Falconer.Regularization.nonendpoint_source_class_middle_pruning: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Falconer.Regularization.nonendpoint_source_class_middle_pruning` of [lean/OAI/MeasureTheory/Falconer/Radial/NonendpointSourceMiddle.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Radial/NonendpointSourceMiddle.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Falconer.Regularization`, with `open Set MeasureTheory NormedSpace`, `open scoped ENNReal`):
--
--   ```lean
--   theorem nonendpoint_source_class_middle_pruning (hpublished : PublishedPlanarFurstenberg)
--       {h : ℕ} {t q : ℝ} (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2)
--       (hqt : q < t) (ht : t-(h:ℝ) < 1) :
--       ∃ ε b : ℝ, 0 < ε ∧ 0 < b ∧ ∃ M₀ : ℕ, ∀ M ≥ M₀,
--         ∀ (Q : DyadicCube (h+2)), Q.side = 1 →
--         ∀ (μ ν : Measure (Space (h+2))) [IsProbabilityMeasure μ] [IsFiniteMeasure ν],
--         ν univ ≤ 1 → ∀ N B : ℕ, 0 < N → 0 < B →
--         ∀ lam E σ : ℝ, 0 ≤ E → 0 ≤ lam → 0 < σ → σ ≤ 1 → σ*Real.sqrt (h+2:ℕ) ≤ 1/4 →
--         (B:ℝ) ≤ lam*(N:ℝ) → (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam →
--         ∀ p₀ ∈ regularizationLeaves Q μ N, ∀ p v : ℕ, p ≤ v → v ≤ N → M ≤ v-p →
--         ∀ P : CellPath (h+2), P.length = p →
--         0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier →
--         (∀ n, p ≤ n → n ≤ v →
--           t*(n-p:ℕ)/N-E ≤ sourceProfile Q μ N B p₀ n-sourceProfile Q μ N B p₀ p) →
--         (((((2*Nat.ceil (2+4*Real.sqrt (h+2:ℕ))+1)^(h+2):ℕ):ℝ)*(2:ℝ)^t*
--           ((2:ℝ)^N)^(E+2*(((h+2:ℕ):ℝ)+1)*lam))*σ^(-t)) ≤ (1/(2:ℝ)^M)^(-ε) →
--         ∀ (_w₀ : Sphere (h+2)) (G : Set (Space (h+2) × Space (h+2))), MeasurableSet G →
--         (∀ z x, (z,x) ∈ G → z ≠ x ∧ z ∈ (Q.descendant P).carrier) →
--         (∀ᵐ z ∂ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier,
--           ∀ w : Sphere (h+2), ∀ j : ℕ, j ≤ M →
--           ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) (w:Space (h+2)) < 1/(2:ℝ)^j} ≤
--             ENNReal.ofReal ((1/(2:ℝ)^M)^(-ε)*(1/(2:ℝ)^j)^q)) →
--         ∀ r H θ : ℝ, 0 < r → 8*(1/4:ℝ)^2/((σ*(2:ℝ)^p)*r) ≤ 1/(2:ℝ)^M →
--         ((σ*(2:ℝ)^p)*H)*θ ≤ 1/(2:ℝ)^M →
--         (∀ x, (∃ z, (z,x) ∈ G) → r ≤ ‖(Q.descendant P).center-x‖ ∧
--           ∀ᵐ y ∂ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier, ‖y-x‖ ≤ H) →
--         ∃ G' : Set (Space (h+2) × Space (h+2)), MeasurableSet G' ∧ G' ⊆ G ∧
--           ((ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier).prod ν)
--             (G \ G') ≤ 2*ENNReal.ofReal ((1/(2:ℝ)^M)^b) ∧
--           ∀ z ∈ G', radialCollisionMass
--             (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier) θ z ≤
--               ENNReal.ofReal ((1/(2:ℝ)^M)^(q+b/2))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Falconer.DyadicCube`, `OAI.Falconer.Space`, `OAI.Falconer.Sphere`, `OAI.Falconer.DyadicCube.carrier`, `OAI.Falconer.DyadicCube.center`, `OAI.Falconer.DyadicCube.descendant` and `OAI.Falconer.Regularization.CellPath` (definitions bundle `OAIQ088F000` of this split); `OAI.Falconer.PublishedPlanarFurstenberg`, `OAI.Falconer.radialCollisionMass`, `OAI.Falconer.Regularization.regularizationLeaves`, `OAI.Falconer.Regularization.sourceClass` and `OAI.Falconer.Regularization.sourceProfile` (definitions bundle `OAIQ088F002` of this split).
--
--   **Used by.** The proofs of `OAI_Falconer_CapAvailable_nonendpoint_improve`, `OAI_Falconer_Regularization_nonendpoint_contact_gain` and `OAI.Falconer.Regularization.nonendpoint_one_scale_gain` of this split import it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Radial/NonendpointSourceMiddle.lean (declaration OAI.Falconer.Regularization.nonendpoint_source_class_middle_pruning)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002

section

attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem nonendpoint_source_class_middle_pruning (hpublished : PublishedPlanarFurstenberg)
    {h : ℕ} {t q : ℝ} (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2)
    (hqt : q < t) (ht : t-(h:ℝ) < 1) :
    ∃ ε b : ℝ, 0 < ε ∧ 0 < b ∧ ∃ M₀ : ℕ, ∀ M ≥ M₀,
      ∀ (Q : DyadicCube (h+2)), Q.side = 1 →
      ∀ (μ ν : Measure (Space (h+2))) [IsProbabilityMeasure μ] [IsFiniteMeasure ν],
      ν univ ≤ 1 → ∀ N B : ℕ, 0 < N → 0 < B →
      ∀ lam E σ : ℝ, 0 ≤ E → 0 ≤ lam → 0 < σ → σ ≤ 1 → σ*Real.sqrt (h+2:ℕ) ≤ 1/4 →
      (B:ℝ) ≤ lam*(N:ℝ) → (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam →
      ∀ p₀ ∈ regularizationLeaves Q μ N, ∀ p v : ℕ, p ≤ v → v ≤ N → M ≤ v-p →
      ∀ P : CellPath (h+2), P.length = p →
      0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier →
      (∀ n, p ≤ n → n ≤ v →
        t*(n-p:ℕ)/N-E ≤ sourceProfile Q μ N B p₀ n-sourceProfile Q μ N B p₀ p) →
      (((((2*Nat.ceil (2+4*Real.sqrt (h+2:ℕ))+1)^(h+2):ℕ):ℝ)*(2:ℝ)^t*
        ((2:ℝ)^N)^(E+2*(((h+2:ℕ):ℝ)+1)*lam))*σ^(-t)) ≤ (1/(2:ℝ)^M)^(-ε) →
      ∀ (_w₀ : Sphere (h+2)) (G : Set (Space (h+2) × Space (h+2))), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → z ≠ x ∧ z ∈ (Q.descendant P).carrier) →
      (∀ᵐ z ∂ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier,
        ∀ w : Sphere (h+2), ∀ j : ℕ, j ≤ M →
        ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) (w:Space (h+2)) < 1/(2:ℝ)^j} ≤
          ENNReal.ofReal ((1/(2:ℝ)^M)^(-ε)*(1/(2:ℝ)^j)^q)) →
      ∀ r H θ : ℝ, 0 < r → 8*(1/4:ℝ)^2/((σ*(2:ℝ)^p)*r) ≤ 1/(2:ℝ)^M →
      ((σ*(2:ℝ)^p)*H)*θ ≤ 1/(2:ℝ)^M →
      (∀ x, (∃ z, (z,x) ∈ G) → r ≤ ‖(Q.descendant P).center-x‖ ∧
        ∀ᵐ y ∂ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier, ‖y-x‖ ≤ H) →
      ∃ G' : Set (Space (h+2) × Space (h+2)), MeasurableSet G' ∧ G' ⊆ G ∧
        ((ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier).prod ν)
          (G \ G') ≤ 2*ENNReal.ofReal ((1/(2:ℝ)^M)^b) ∧
        ∀ z ∈ G', radialCollisionMass
          (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier) θ z ≤
            ENNReal.ofReal ((1/(2:ℝ)^M)^(q+b/2)) := by
  sorry

end Falconer.Regularization

end OAI
end
