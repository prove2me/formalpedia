-- Prove2me | Theorems.Thm_OAI_AffineBernstein_normalized_model_uniform_actual_sigma
-- name    : OAI.AffineBernstein.normalized_model_uniform_actual_sigma
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:11:23.327007+00:00
-- url     : https://prove2.me/theorems/1cc43bf2-a217-4aad-b01f-d036fc1c5505
-- title:
--   OAI.AffineBernstein.normalized_model_uniform_actual_sigma: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.normalized_model_uniform_actual_sigma` of [lean/OAI/Analysis/AffineBernstein/NormalizedSigma.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/NormalizedSigma.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open Metric Filter`):
--
--   ```lean
--   theorem normalized_model_uniform_actual_sigma {n k m d : ℕ}
--       (hn : 1 ≤ n) (hk : 1 ≤ k) (hm : 1 ≤ m)
--       (e : Fin n ≃ Fin k ⊕ Fin d) (eE : Fin m ≃ Fin d ⊕ Unit)
--       (f : WithLp 2 (Space d × ℝ) ≃ₗᵢ[ℝ] Space m)
--       {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) :
--       ∃ Cσ : ℝ≥0∞, Cσ ≠ ⊤ ∧ ∀ {Ω : Set (Space n)}, IsOpen Ω → Ω.Nonempty → Convex ℝ Ω →
--         ∀ {u : Space n → ℝ}, ContDiffOn ℝ ∞ u Ω →
--         (∀ x ∈ Ω, (hessian u x).PosDef) → AffineMaximalOn Ω u → EuclideanGraphComplete Ω u →
--         ∀ (a : ℕ → Space n × ℝ) (L : ℕ → (Space k × Space m) ≃L[ℝ] (Space n × ℝ))
--         (C : Set (Space k × Space m)), IsModelShape C →
--         closedBall 0 r ⊆ modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) →
--         modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) ⊆ closedBall 0 R →
--         LocalDistanceConverges (fun j => affineEpigraphPullback Ω u (a j) (L j)) C →
--         ∀ᶠ j in atTop,
--         let H := fun q : Space k × Space m =>
--           homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u (a j) (L j)} q.2
--         let bE := (EuclideanSpace.basisFun (Fin m) ℝ).reindex eE
--         (∫⁻ q : Space k × Metric.sphere (0:Space m) 1,
--           ENNReal.ofReal (tubeMeasureDensity n H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bE
--             (q.1,q.2) * tubeLogMassWeight H (q.1,q.2))
--           ∂(volume.restrict (normalizedCell k)).prod (volume : Measure (Space m)).toSphere) ≤ Cσ
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.IsModelShape`, `OAI.AffineBernstein.LocalDistanceConverges`, `OAI.AffineBernstein.affineEpigraphPullback`, `OAI.AffineBernstein.homogeneousSupport`, `OAI.AffineBernstein.modelFiber`, `OAI.AffineBernstein.normalizedCell`, `OAI.AffineBernstein.tubeLogMassWeight` and `OAI.AffineBernstein.tubeMeasureDensity` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.AffineMaximalOn`, `OAI.AffineBernstein.EuclideanGraphComplete`, `OAI.AffineBernstein.Space` and `OAI.AffineBernstein.hessian` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proof of `OAI.AffineBernstein.affineMaximal_no_normalized_maximal_model` of this split imports it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/NormalizedSigma.lean (declaration OAI.AffineBernstein.normalized_model_uniform_actual_sigma)

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

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

open Metric Filter

theorem normalized_model_uniform_actual_sigma {n k m d : ℕ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (e : Fin n ≃ Fin k ⊕ Fin d) (eE : Fin m ≃ Fin d ⊕ Unit)
    (f : WithLp 2 (Space d × ℝ) ≃ₗᵢ[ℝ] Space m)
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) :
    ∃ Cσ : ℝ≥0∞, Cσ ≠ ⊤ ∧ ∀ {Ω : Set (Space n)}, IsOpen Ω → Ω.Nonempty → Convex ℝ Ω →
      ∀ {u : Space n → ℝ}, ContDiffOn ℝ ∞ u Ω →
      (∀ x ∈ Ω, (hessian u x).PosDef) → AffineMaximalOn Ω u → EuclideanGraphComplete Ω u →
      ∀ (a : ℕ → Space n × ℝ) (L : ℕ → (Space k × Space m) ≃L[ℝ] (Space n × ℝ))
      (C : Set (Space k × Space m)), IsModelShape C →
      closedBall 0 r ⊆ modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) →
      modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) ⊆ closedBall 0 R →
      LocalDistanceConverges (fun j => affineEpigraphPullback Ω u (a j) (L j)) C →
      ∀ᶠ j in atTop,
      let H := fun q : Space k × Space m =>
        homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u (a j) (L j)} q.2
      let bE := (EuclideanSpace.basisFun (Fin m) ℝ).reindex eE
      (∫⁻ q : Space k × Metric.sphere (0:Space m) 1,
        ENNReal.ofReal (tubeMeasureDensity n H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bE
          (q.1,q.2) * tubeLogMassWeight H (q.1,q.2))
        ∂(volume.restrict (normalizedCell k)).prod (volume : Measure (Space m)).toSphere) ≤ Cσ := by
  sorry

end AffineBernstein

end

end OAI
end
