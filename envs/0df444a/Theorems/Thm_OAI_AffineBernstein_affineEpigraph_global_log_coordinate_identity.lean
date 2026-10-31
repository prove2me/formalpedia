-- Prove2me | Theorems.Thm_OAI_AffineBernstein_affineEpigraph_global_log_coordinate_identity
-- name    : OAI.AffineBernstein.affineEpigraph_global_log_coordinate_identity
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:04:35.740206+00:00
-- url     : https://prove2.me/theorems/51a6a3e3-48ea-41e8-8d47-6d43f03e0ae0
-- title:
--   OAI.AffineBernstein.affineEpigraph_global_log_coordinate_identity: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.affineEpigraph_global_log_coordinate_identity` of [lean/OAI/Analysis/AffineBernstein/LinearLogTrace.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/LinearLogTrace.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open Metric`):
--
--   ```lean
--   theorem affineEpigraph_global_log_coordinate_identity {n : ℕ} {Ω : Set (Space n)}
--       (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
--       (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
--       (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
--       {D : Set S} (hD : IsOpen D)
--       (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
--       (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
--       (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
--       (ℓ : S →L[ℝ] ℝ) (hℓ : ∀ s ∈ D, 0 < ℓ s)
--       {σ : S → ℝ} (hσ : ContDiff ℝ ∞ σ) (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D)
--       :
--       let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
--       let P := fun q => Real.log (H q)
--       let F := invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))
--       let M := tubeMeasureDensity n H bS bE
--       let A := fun q : S × E => Real.log (ℓ q.1)
--       tubeIntegral μ M (fun s => σ s^2) (fun q => tubeBasePair H bS A A q+
--         (n : ℝ)*tubeBasePair H bS P A q+(((n : ℝ)+2)/2)*tubeBasePair H bS F A q) =
--         2*tubeIntegral μ M σ (tubeBasePair H bS (fun q => σ q.1) A)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.affineEpigraphPullback`, `OAI.AffineBernstein.homogeneousSupport`, `OAI.AffineBernstein.invariantTubeF`, `OAI.AffineBernstein.tubeBasePair`, `OAI.AffineBernstein.tubeIntegral` and `OAI.AffineBernstein.tubeMeasureDensity` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.Space` and `OAI.AffineBernstein.hessian` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proof of `OAI.AffineBernstein.affineMaximal_no_polynomial_logMeasure` of this split imports it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/LinearLogTrace.lean (declaration OAI.AffineBernstein.affineEpigraph_global_log_coordinate_identity)

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

section ActualLogCoordinate
open Metric
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure S} [μ.IsAddHaarMeasure]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem affineEpigraph_global_log_coordinate_identity {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (ℓ : S →L[ℝ] ℝ) (hℓ : ∀ s ∈ D, 0 < ℓ s)
    {σ : S → ℝ} (hσ : ContDiff ℝ ∞ σ) (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D)
    :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let P := fun q => Real.log (H q)
    let F := invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))
    let M := tubeMeasureDensity n H bS bE
    let A := fun q : S × E => Real.log (ℓ q.1)
    tubeIntegral μ M (fun s => σ s^2) (fun q => tubeBasePair H bS A A q+
      (n : ℝ)*tubeBasePair H bS P A q+(((n : ℝ)+2)/2)*tubeBasePair H bS F A q) =
      2*tubeIntegral μ M σ (tubeBasePair H bS (fun q => σ q.1) A) := by
  sorry

end ActualLogCoordinate

end AffineBernstein
end

end OAI
end
