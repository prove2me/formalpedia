-- Prove2me | Theorems.Thm_OAI_AffineBernstein_affineEpigraph_tube_angular_smooth
-- name    : OAI.AffineBernstein.affineEpigraph_tube_angular_smooth
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:06:46.364203+00:00
-- url     : https://prove2.me/theorems/e1822972-cb48-404f-b71b-b50c537da7e7
-- title:
--   OAI.AffineBernstein.affineEpigraph_tube_angular_smooth: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.affineEpigraph_tube_angular_smooth` of [lean/OAI/Analysis/AffineBernstein/ActualWeightedAngular.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/ActualWeightedAngular.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open Metric`):
--
--   ```lean
--   lemma affineEpigraph_tube_angular_smooth {n : ℕ} {Ω : Set (Space n)}
--       (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
--       (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
--       (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
--       {D : Set S} (hD : IsOpen D)
--       (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
--       (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
--       {s : S} (hs : s ∈ D)
--       (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) (δ : ℝ) :
--       let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
--       let P := fun q => Real.log (H q)
--       let F := invariantTubeF H bS bE δ
--       ContDiffOn ℝ ∞ (fun e => H (s,e)) {e | e ≠ 0} ∧
--       ContDiffOn ℝ ∞ (fun e => P (s,e)) {e | e ≠ 0} ∧
--       ContDiffOn ℝ ∞ (fun e => F (s,e)) {e | e ≠ 0} ∧
--       (∀ e ∈ {e : E | e ≠ 0}, ∀ v, fderiv ℝ (fderiv ℝ (fun y => H (s,y))) e v e = 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.affineEpigraphPullback`, `OAI.AffineBernstein.homogeneousSupport` and `OAI.AffineBernstein.invariantTubeF` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.Space` and `OAI.AffineBernstein.hessian` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proof of `OAI.AffineBernstein.affineEpigraph_angular_literal_drift` of this split imports it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/ActualWeightedAngular.lean (declaration OAI.AffineBernstein.affineEpigraph_tube_angular_smooth)

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

omit [MeasurableSpace E] [BorelSpace E] in
lemma affineEpigraph_tube_angular_smooth {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) (δ : ℝ) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let P := fun q => Real.log (H q)
    let F := invariantTubeF H bS bE δ
    ContDiffOn ℝ ∞ (fun e => H (s,e)) {e | e ≠ 0} ∧
    ContDiffOn ℝ ∞ (fun e => P (s,e)) {e | e ≠ 0} ∧
    ContDiffOn ℝ ∞ (fun e => F (s,e)) {e | e ≠ 0} ∧
    (∀ e ∈ {e : E | e ≠ 0}, ∀ v, fderiv ℝ (fderiv ℝ (fun y => H (s,y))) e v e = 0) := by
  sorry

end AffineBernstein
end

end OAI
end
