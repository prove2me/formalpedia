-- Prove2me | Theorems.Thm_OAI_AffineBernstein_normalized_model_positive_log_mass
-- name    : OAI.AffineBernstein.normalized_model_positive_log_mass
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:11:24.478344+00:00
-- url     : https://prove2.me/theorems/29de5433-444b-4328-a637-ab9d2bfb498d
-- title:
--   OAI.AffineBernstein.normalized_model_positive_log_mass: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.normalized_model_positive_log_mass` of [lean/OAI/Analysis/AffineBernstein/ModelPositiveLogMass.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/ModelPositiveLogMass.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open Metric Filter`):
--
--   ```lean
--   theorem normalized_model_positive_log_mass {n k m d : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
--       (hm : 1 ≤ m) (e : Fin n ≃ Fin k ⊕ Fin d) (eE : Fin m ≃ Fin d ⊕ Unit)
--       (f : WithLp 2 (Space d × ℝ) ≃ₗᵢ[ℝ] Space m)
--       {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
--       {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
--       (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hmP : AffineMaximalOn Ω u)
--       (hcomplete : EuclideanGraphComplete Ω u)
--       (a : ℕ → Space n × ℝ) (L : ℕ → (Space k × Space m) ≃L[ℝ] (Space n × ℝ))
--       {C : Set (Space k × Space m)} (hC : IsModelShape C)
--       (hlim : LocalDistanceConverges (fun j => affineEpigraphPullback Ω u (a j) (L j)) C)
--       {r R₀ : ℝ} (hr : 0 < r)
--       (hin : closedBall (0:Space m) r ⊆ modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))))
--       (hout : modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) ⊆ closedBall 0 R₀) :
--       ∃ T : ℕ, ∃ c > 0, ∀ᶠ j in atTop,
--         c ≤ (affineEpigraphLogMeasure volume
--           (regularPositiveFiberDomain (affineEpigraphPullback Ω u (a j) (L j))) Ω u (a j) (L j)
--           ((EuclideanSpace.basisFun (Fin m) ℝ).reindex eE)).real (logarithmicBox k T)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.IsModelShape`, `OAI.AffineBernstein.LocalDistanceConverges`, `OAI.AffineBernstein.affineEpigraphLogMeasure`, `OAI.AffineBernstein.affineEpigraphPullback`, `OAI.AffineBernstein.logarithmicBox`, `OAI.AffineBernstein.modelFiber` and `OAI.AffineBernstein.regularPositiveFiberDomain` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.AffineMaximalOn`, `OAI.AffineBernstein.EuclideanGraphComplete`, `OAI.AffineBernstein.Space` and `OAI.AffineBernstein.hessian` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proof of `OAI.AffineBernstein.affineMaximal_no_normalized_maximal_model` of this split imports it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/ModelPositiveLogMass.lean (declaration OAI.AffineBernstein.normalized_model_positive_log_mass)

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
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section ModelPositiveLogMass
open Metric Filter

theorem normalized_model_positive_log_mass {n k m d : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hm : 1 ≤ m) (e : Fin n ≃ Fin k ⊕ Fin d) (eE : Fin m ≃ Fin d ⊕ Unit)
    (f : WithLp 2 (Space d × ℝ) ≃ₗᵢ[ℝ] Space m)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hmP : AffineMaximalOn Ω u)
    (hcomplete : EuclideanGraphComplete Ω u)
    (a : ℕ → Space n × ℝ) (L : ℕ → (Space k × Space m) ≃L[ℝ] (Space n × ℝ))
    {C : Set (Space k × Space m)} (hC : IsModelShape C)
    (hlim : LocalDistanceConverges (fun j => affineEpigraphPullback Ω u (a j) (L j)) C)
    {r R₀ : ℝ} (hr : 0 < r)
    (hin : closedBall (0:Space m) r ⊆ modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))))
    (hout : modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) ⊆ closedBall 0 R₀) :
    ∃ T : ℕ, ∃ c > 0, ∀ᶠ j in atTop,
      c ≤ (affineEpigraphLogMeasure volume
        (regularPositiveFiberDomain (affineEpigraphPullback Ω u (a j) (L j))) Ω u (a j) (L j)
        ((EuclideanSpace.basisFun (Fin m) ℝ).reindex eE)).real (logarithmicBox k T) := by
  sorry
end ModelPositiveLogMass

end
end AffineBernstein
end

end OAI
end
