-- Prove2me | Theorems.Thm_OAI_CriticalSK_orientation_normalized_overlap_bound
-- name    : OAI.CriticalSK.orientation_normalized_overlap_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T02:31:36.887008+00:00
-- url     : https://prove2.me/theorems/493f144e-2710-49c4-8470-dd1bd4714316
-- title:
--   OAI.CriticalSK.orientation_normalized_overlap_bound: intermediate lemma from OpenAI, Critical slowing down in the Sherrington–Kirkpatrick model
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalSK.covariance_and_linear_tests` and `OAI.CriticalSK.critical_mixing_lower_bounds`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical slowing down in the Sherrington–Kirkpatrick model*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalSK.orientation_normalized_overlap_bound` of [lean/OAI/MathematicalPhysics/CriticalSK/OrientationBounds.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/OrientationBounds.lean) at commit adc7f12, ported to this platform's Lean and Mathlib.
--
--   **The statement**, as published (namespace `OAI.CriticalSK`, with `open scoped BigOperators Topology NNReal ENNReal`, `open scoped BigOperators ENNReal NNReal Real Topology`, `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal`, `open scoped BigOperators NNReal`, `open scoped BigOperators`, `open scoped BigOperators InnerProductSpace`, `open Module`, `open Matrix Polynomial`, `open scoped BigOperators Topology`, `open Filter`, `open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise`, `open Set Metric MeasureTheory MeasureTheory.Measure`, `open scoped ENNReal NNReal BigOperators`, `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal Topology`, `open MeasureTheory MeasureTheory.Measure Set Metric`, `open scoped NNReal ENNReal BigOperators`, `open scoped NNReal ENNReal`, `open ProbabilityTheory`, `open Metric Set MeasureTheory`, `open scoped ENNReal Pointwise`, `open MeasureTheory Filter Set Real`, `open Finset Real`, `open scoped BigOperators ENNReal Topology`, `open Set MeasureTheory`, `open scoped BigOperators ENNReal`, `open MeasureTheory`, `open Finset Real Filter`, `open scoped Topology`, `open Set MeasureTheory Filter`):
--
--   ```lean
--   lemma orientation_normalized_overlap_bound (ε : ℝ) (hε : 0 < ε) :
--       ∀ᶠ n : ℕ in atTop, ∀ [Nonempty (Fin n)] (lam : Fin n → ℝ) (u v : EuclideanSpace ℝ (Fin n)) (K s₀ : ℝ),
--         ‖u‖ = Real.sqrt n → ‖v‖ = Real.sqrt n → inner ℝ u v = 0 →
--         (∀ i, |lam i| ≤ 3) → 0 < K →
--         K*Real.exp ((n:ℝ)*sphericalVariational lam 1) ≤ spherePartition lam 1 (Real.sqrt n) →
--         0 ≤ s₀ → spectralTop lam < 2+s₀ → 2-s₀ ≤ spectralTop lam →
--         spectralStieltjes lam (2+s₀) ≤ 1 →
--         (∀ s ∈ Set.Icc s₀ 1, |spectralStieltjes lam (2+s)-semicircleResolvent s| ≤ (1/100)*Real.sqrt s) →
--         216*s₀ ≤ overlapCentralCutoff n^2 →
--         saddleSubcriticalError lam+s₀/2 ≤ 1/1536 →
--         (∫ U, rotatedCubePair lam (fun q => q^2) U ∂orthogonalHaar (Fin n)) /
--           spherePartition lam 1 (Real.sqrt n)^2 ≤
--           (1+ε)*((∫ q : ℝ, (q^2*pairMoment lam u v q)*sphereOverlapDensity n q) /
--             spherePartition lam 1 (Real.sqrt n)^2)+
--           (n+1)*((26*Real.exp 1*n/K)^2 * Real.exp (-(n:ℝ)/24*overlapCentralCutoff n^3))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalSK.orthogonalGroup_measurableSpace`, `OAI.CriticalSK.orthogonalHaar`, `OAI.CriticalSK.overlapCentralCutoff`, `OAI.CriticalSK.pairMoment`, `OAI.CriticalSK.saddleSubcriticalError`, `OAI.CriticalSK.semicircleResolvent`, `OAI.CriticalSK.spectralStieltjes`, `OAI.CriticalSK.spectralTop`, `OAI.CriticalSK.sphereOverlapDensity`, `OAI.CriticalSK.spherePartition` and `OAI.CriticalSK.sphericalVariational` (definitions bundle `OAIQWCSK000` of this split); `OAI.CriticalSK.rotatedCubePair` (definitions bundle `OAIQWCSK001` of this split).
--
--   **Used by.** The proofs of `OAI.CriticalSK.cavity_overlap_tail_zero` and `OAI.CriticalSK.covariance_upper_tight` of this split import it.
-- source:
--   OpenAI, Critical slowing down in the Sherrington–Kirkpatrick model, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-slowing-down-in-the-Sherrington-Kirkpatrick-model-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/OrientationBounds.lean (declaration OAI.CriticalSK.orientation_normalized_overlap_bound)

import Mathlib
import Definitions.Def_OAIQWCSK001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal

open scoped BigOperators NNReal

open scoped BigOperators

open scoped BigOperators InnerProductSpace

open Module

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal BigOperators

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open scoped NNReal ENNReal BigOperators

open scoped NNReal ENNReal

open ProbabilityTheory

open Metric Set MeasureTheory

open scoped ENNReal Pointwise

open MeasureTheory Filter Set Real

open Finset Real
open scoped BigOperators ENNReal Topology
open Set MeasureTheory
open scoped BigOperators ENNReal
open MeasureTheory
open Finset Real Filter
open scoped Topology
namespace CriticalSK

open Set MeasureTheory Filter

lemma orientation_normalized_overlap_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ [Nonempty (Fin n)] (lam : Fin n → ℝ) (u v : EuclideanSpace ℝ (Fin n)) (K s₀ : ℝ),
      ‖u‖ = Real.sqrt n → ‖v‖ = Real.sqrt n → inner ℝ u v = 0 →
      (∀ i, |lam i| ≤ 3) → 0 < K →
      K*Real.exp ((n:ℝ)*sphericalVariational lam 1) ≤ spherePartition lam 1 (Real.sqrt n) →
      0 ≤ s₀ → spectralTop lam < 2+s₀ → 2-s₀ ≤ spectralTop lam →
      spectralStieltjes lam (2+s₀) ≤ 1 →
      (∀ s ∈ Set.Icc s₀ 1, |spectralStieltjes lam (2+s)-semicircleResolvent s| ≤ (1/100)*Real.sqrt s) →
      216*s₀ ≤ overlapCentralCutoff n^2 →
      saddleSubcriticalError lam+s₀/2 ≤ 1/1536 →
      (∫ U, rotatedCubePair lam (fun q => q^2) U ∂orthogonalHaar (Fin n)) /
        spherePartition lam 1 (Real.sqrt n)^2 ≤
        (1+ε)*((∫ q : ℝ, (q^2*pairMoment lam u v q)*sphereOverlapDensity n q) /
          spherePartition lam 1 (Real.sqrt n)^2)+
        (n+1)*((26*Real.exp 1*n/K)^2 * Real.exp (-(n:ℝ)/24*overlapCentralCutoff n^3)) := by
  sorry

end CriticalSK

end

end OAI
end
