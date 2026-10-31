-- Prove2me | Theorems.Thm_OAI_AffineBernstein_affineEpigraph_sigma_normalization
-- name    : OAI.AffineBernstein.affineEpigraph_sigma_normalization
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:06:01.887648+00:00
-- url     : https://prove2.me/theorems/1efa3983-f612-484d-8bc4-909ef9342ae0
-- title:
--   OAI.AffineBernstein.affineEpigraph_sigma_normalization: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.affineEpigraph_sigma_normalization` of [lean/OAI/Analysis/AffineBernstein/NormalizedSigmaTransport.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/NormalizedSigmaTransport.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open Filter Metric`):
--
--   ```lean
--   theorem affineEpigraph_sigma_normalization {n k m d : ℕ} (hm : 1 ≤ m)
--       (hn : n = k+d) (bE : OrthonormalBasis (Fin d ⊕ Unit) ℝ (Space m))
--       {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
--       (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
--       (a : Space n × ℝ) (L : (Space k × Space m) ≃L[ℝ] (Space n × ℝ))
--       (B : Space k ≃L[ℝ] Space k) (A : Space m ≃L[ℝ] Space m)
--       (coeff : Fin k → ℝ) (hcoeff : ∀ i, coeff i ≠ 0) (hB : ∀ s i, B s i = coeff i*s i)
--       {D : Set (Space k)} (hD : IsOpen D)
--       {Q : Set (Space k)} (hQ : MeasurableSet Q) (hQD : B '' Q ⊆ D)
--       (hs : ∀ s ∈ Q, ∀ i, s i ≠ 0)
--       (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈
--         affineEpigraphPullback Ω u a ((B.prodCongr A).symm.trans L)})
--       (hzero : ∀ s ∈ D, (0 : Space m) ∈ interior {y | (s,y) ∈
--         affineEpigraphPullback Ω u a ((B.prodCongr A).symm.trans L)}) :
--       let H := fun q : Space k × Space m =>
--         homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
--       let H' := fun q : Space k × Space m => homogeneousSupport {y | (q.1,y) ∈
--         affineEpigraphPullback Ω u a ((B.prodCongr A).symm.trans L)} q.2
--       let bS := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
--       (∫⁻ q : Space k × Metric.sphere (0:Space m) 1,
--         ENNReal.ofReal (tubeMeasureDensity n H bS bE (q.1,q.2)*tubeLogMassWeight H (q.1,q.2))
--         ∂(volume.restrict Q).prod (volume : Measure (Space m)).toSphere) =
--       (∫⁻ q : Space k × Metric.sphere (0:Space m) 1,
--         ENNReal.ofReal (tubeMeasureDensity n H' bS bE (q.1,q.2)*tubeLogMassWeight H' (q.1,q.2))
--         ∂(volume.restrict (B '' Q)).prod (volume : Measure (Space m)).toSphere)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.affineEpigraphPullback`, `OAI.AffineBernstein.homogeneousSupport`, `OAI.AffineBernstein.tubeLogMassWeight` and `OAI.AffineBernstein.tubeMeasureDensity` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.Space` and `OAI.AffineBernstein.hessian` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proof of `OAI.AffineBernstein.affineMaximal_no_normalized_maximal_model` of this split imports it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/NormalizedSigmaTransport.lean (declaration OAI.AffineBernstein.affineEpigraph_sigma_normalization)

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

section NormalizedSigmaTransport
open Filter Metric

theorem affineEpigraph_sigma_normalization {n k m d : ℕ} (hm : 1 ≤ m)
    (hn : n = k+d) (bE : OrthonormalBasis (Fin d ⊕ Unit) ℝ (Space m))
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (Space k × Space m) ≃L[ℝ] (Space n × ℝ))
    (B : Space k ≃L[ℝ] Space k) (A : Space m ≃L[ℝ] Space m)
    (coeff : Fin k → ℝ) (hcoeff : ∀ i, coeff i ≠ 0) (hB : ∀ s i, B s i = coeff i*s i)
    {D : Set (Space k)} (hD : IsOpen D)
    {Q : Set (Space k)} (hQ : MeasurableSet Q) (hQD : B '' Q ⊆ D)
    (hs : ∀ s ∈ Q, ∀ i, s i ≠ 0)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈
      affineEpigraphPullback Ω u a ((B.prodCongr A).symm.trans L)})
    (hzero : ∀ s ∈ D, (0 : Space m) ∈ interior {y | (s,y) ∈
      affineEpigraphPullback Ω u a ((B.prodCongr A).symm.trans L)}) :
    let H := fun q : Space k × Space m =>
      homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let H' := fun q : Space k × Space m => homogeneousSupport {y | (q.1,y) ∈
      affineEpigraphPullback Ω u a ((B.prodCongr A).symm.trans L)} q.2
    let bS := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
    (∫⁻ q : Space k × Metric.sphere (0:Space m) 1,
      ENNReal.ofReal (tubeMeasureDensity n H bS bE (q.1,q.2)*tubeLogMassWeight H (q.1,q.2))
      ∂(volume.restrict Q).prod (volume : Measure (Space m)).toSphere) =
    (∫⁻ q : Space k × Metric.sphere (0:Space m) 1,
      ENNReal.ofReal (tubeMeasureDensity n H' bS bE (q.1,q.2)*tubeLogMassWeight H' (q.1,q.2))
      ∂(volume.restrict (B '' Q)).prod (volume : Measure (Space m)).toSphere) := by
  sorry
end NormalizedSigmaTransport

end AffineBernstein
end

end OAI
end
