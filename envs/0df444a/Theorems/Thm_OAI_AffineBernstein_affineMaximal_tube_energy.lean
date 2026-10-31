-- Prove2me | Theorems.Thm_OAI_AffineBernstein_affineMaximal_tube_energy
-- name    : OAI.AffineBernstein.affineMaximal_tube_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:08:46.123049+00:00
-- url     : https://prove2.me/theorems/074d3de6-7390-474d-b789-e9d0dd8ee135
-- title:
--   OAI.AffineBernstein.affineMaximal_tube_energy: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.affineMaximal_tube_energy` of [lean/OAI/Analysis/AffineBernstein/ActualTubeEnergy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/ActualTubeEnergy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open Metric`):
--
--   ```lean
--   theorem affineMaximal_tube_energy {n : ℕ} (hn : 3 ≤ n) (hn9 : n ≤ 9) {Ω : Set (Space n)}
--       (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
--       (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
--       (hm : AffineMaximalOn Ω u)
--       (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
--       {D : Set S} (hD : IsOpen D)
--       (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
--       (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
--       (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
--       (hk : 2 ≤ Fintype.card ι)
--       {σ : S → ℝ} (hσ : ContDiff ℝ ∞ σ) (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D) :
--       let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
--       let P := fun q => Real.log (H q)
--       let F := invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))
--       let M := tubeMeasureDensity n H bS bE
--       tubeIntegral μ M (fun s => σ s^2) (fun q => 1+tubeBasePair H bS P P q+
--         tubeBasePair H bS F F q+tubeAngularPair H bE F F q) ≤
--         4194304*tubeIntegral μ M (fun _ => 1) (tubeBasePair H bS (fun q => σ q.1) (fun q => σ q.1))
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.affineEpigraphPullback`, `OAI.AffineBernstein.homogeneousSupport`, `OAI.AffineBernstein.invariantTubeF`, `OAI.AffineBernstein.tubeAngularPair`, `OAI.AffineBernstein.tubeBasePair`, `OAI.AffineBernstein.tubeIntegral` and `OAI.AffineBernstein.tubeMeasureDensity` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.AffineMaximalOn`, `OAI.AffineBernstein.Space` and `OAI.AffineBernstein.hessian` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proof of `OAI.AffineBernstein.affineMaximal_no_polynomial_logMeasure` of this split imports it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/ActualTubeEnergy.lean (declaration OAI.AffineBernstein.affineMaximal_tube_energy)

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

open Metric
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure S} [μ.IsAddHaarMeasure]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem affineMaximal_tube_energy {n : ℕ} (hn : 3 ≤ n) (hn9 : n ≤ 9) {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hk : 2 ≤ Fintype.card ι)
    {σ : S → ℝ} (hσ : ContDiff ℝ ∞ σ) (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let P := fun q => Real.log (H q)
    let F := invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))
    let M := tubeMeasureDensity n H bS bE
    tubeIntegral μ M (fun s => σ s^2) (fun q => 1+tubeBasePair H bS P P q+
      tubeBasePair H bS F F q+tubeAngularPair H bE F F q) ≤
      4194304*tubeIntegral μ M (fun _ => 1) (tubeBasePair H bS (fun q => σ q.1) (fun q => σ q.1)) := by
  sorry

end AffineBernstein
end

end OAI
end
