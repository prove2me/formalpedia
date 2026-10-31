-- Prove2me | Theorems.Thm_OAI_AffineBernstein_affineEpigraph_angular_literal_drift
-- name    : OAI.AffineBernstein.affineEpigraph_angular_literal_drift
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:03:19.512673+00:00
-- url     : https://prove2.me/theorems/a514bb49-e481-40e8-b94a-da08efe114b9
-- title:
--   OAI.AffineBernstein.affineEpigraph_angular_literal_drift: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.affineEpigraph_angular_literal_drift` of [lean/OAI/Analysis/AffineBernstein/ActualWeightedAngularFurther.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/ActualWeightedAngularFurther.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open Metric`):
--
--   ```lean
--   theorem affineEpigraph_angular_literal_drift {n : ℕ} {Ω : Set (Space n)}
--       (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
--       (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
--       (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
--       {D : Set S} (hD : IsOpen D)
--       (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
--       (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
--       {s : S} (hs : s ∈ D)
--       (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
--       let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
--       let P := fun q => Real.log (H q)
--       let F := invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))
--       let N := supportNewtonTensor bE (fun e => H (s,e))
--       let dP := fun e => tangentProjection e (gradient (fun y => P (s,y)) e)
--       let dF := fun e => tangentProjection e (gradient (fun y => F (s,y)) e)
--       let W := fun e => tubeMeasureDensity n H bS bE (s,e)*H (s,e)/tubeAngularDensity H (s,e) bE
--       (∫ e : sphere (0:E) 1, W e*roundHessianContraction bE N (fun y => F (s,y)) e ∂volume.toSphere) +
--       2*(∫ e : sphere (0:E) 1, W e*N e (dP e) (dF e) ∂volume.toSphere) +
--       (∫ e : sphere (0:E) 1, W e*N e (dF e) (dF e) ∂volume.toSphere) =
--       (-(n : ℝ)/2)*(∫ e : sphere (0:E) 1, W e*N e (dF e) (dF e) ∂volume.toSphere)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.affineEpigraphPullback`, `OAI.AffineBernstein.homogeneousSupport`, `OAI.AffineBernstein.invariantTubeF`, `OAI.AffineBernstein.roundHessianContraction`, `OAI.AffineBernstein.supportNewtonTensor`, `OAI.AffineBernstein.tangentProjection`, `OAI.AffineBernstein.tubeAngularDensity` and `OAI.AffineBernstein.tubeMeasureDensity` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.Space` and `OAI.AffineBernstein.hessian` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proof of `OAI.AffineBernstein.affineMaximal_global_d_identity` of this split imports it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/ActualWeightedAngularFurther.lean (declaration OAI.AffineBernstein.affineEpigraph_angular_literal_drift)

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
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem affineEpigraph_angular_literal_drift {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let P := fun q => Real.log (H q)
    let F := invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))
    let N := supportNewtonTensor bE (fun e => H (s,e))
    let dP := fun e => tangentProjection e (gradient (fun y => P (s,y)) e)
    let dF := fun e => tangentProjection e (gradient (fun y => F (s,y)) e)
    let W := fun e => tubeMeasureDensity n H bS bE (s,e)*H (s,e)/tubeAngularDensity H (s,e) bE
    (∫ e : sphere (0:E) 1, W e*roundHessianContraction bE N (fun y => F (s,y)) e ∂volume.toSphere) +
    2*(∫ e : sphere (0:E) 1, W e*N e (dP e) (dF e) ∂volume.toSphere) +
    (∫ e : sphere (0:E) 1, W e*N e (dF e) (dF e) ∂volume.toSphere) =
    (-(n : ℝ)/2)*(∫ e : sphere (0:E) 1, W e*N e (dF e) (dF e) ∂volume.toSphere) := by
  sorry

end AffineBernstein
end

end OAI
end
