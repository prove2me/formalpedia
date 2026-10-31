-- Prove2me | Theorems.Thm_OAI_AffineBernstein_affineMaximal_local_chart_stationary
-- name    : OAI.AffineBernstein.affineMaximal_local_chart_stationary
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:08:21.645352+00:00
-- url     : https://prove2.me/theorems/2022e44a-1433-4c9c-8f2b-f6c84c4f0ef3
-- title:
--   OAI.AffineBernstein.affineMaximal_local_chart_stationary: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.affineMaximal_local_chart_stationary` of [lean/OAI/Analysis/AffineBernstein/LocalVelocity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/LocalVelocity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`):
--
--   ```lean
--   theorem affineMaximal_local_chart_stationary {n : ℕ}
--       {Ω K : Set (Space n)} (hΩ : IsOpen Ω) (hK : IsCompact K)
--       (φ : OpenPartialHomeomorph (Space n) (Space n))
--       (hφ : ContDiffOn ℝ ∞ φ φ.source) (hψ : ContDiffOn ℝ ∞ φ.symm φ.target)
--       (hKφ : K ⊆ φ.source) (hφΩ : φ.target ⊆ Ω)
--       {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
--       (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
--       {V : Space n → Space n × ℝ} (hV : ContDiffOn ℝ ∞ V φ.source)
--       (hVK : tsupport V ⊆ K)
--       (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ) :
--       ∃ (β : Space n → ℝ) (a : Fin n → Space n → ℝ),
--         ContDiff ℝ ∞ β ∧ (∀ i, ContDiff ℝ ∞ (a i)) ∧
--         tsupport β ⊆ φ '' K ∧ (∀ i, tsupport (a i) ⊆ φ '' K) ∧
--         (∀ x ∈ φ.source, ∀ t : ℝ,
--           L (graphParamVariation u β a t (φ x))+v =
--             L (φ x,u (φ x))+v+t • V x) ∧
--         HasDerivAt (fun t : ℝ => ∫ x in K,
--           coordinateAffineVariationArea L v φ u β a x t) 0 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.coordinateAffineVariationArea` and `OAI.AffineBernstein.graphParamVariation` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.AffineMaximalOn`, `OAI.AffineBernstein.Space` and `OAI.AffineBernstein.hessian` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proof of `OAI.AffineBernstein.affineMaximal_flatSupport_local_stationary` of this split imports it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/LocalVelocity.lean (declaration OAI.AffineBernstein.affineMaximal_local_chart_stationary)

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

theorem affineMaximal_local_chart_stationary {n : ℕ}
    {Ω K : Set (Space n)} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (φ : OpenPartialHomeomorph (Space n) (Space n))
    (hφ : ContDiffOn ℝ ∞ φ φ.source) (hψ : ContDiffOn ℝ ∞ φ.symm φ.target)
    (hKφ : K ⊆ φ.source) (hφΩ : φ.target ⊆ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    {V : Space n → Space n × ℝ} (hV : ContDiffOn ℝ ∞ V φ.source)
    (hVK : tsupport V ⊆ K)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ) :
    ∃ (β : Space n → ℝ) (a : Fin n → Space n → ℝ),
      ContDiff ℝ ∞ β ∧ (∀ i, ContDiff ℝ ∞ (a i)) ∧
      tsupport β ⊆ φ '' K ∧ (∀ i, tsupport (a i) ⊆ φ '' K) ∧
      (∀ x ∈ φ.source, ∀ t : ℝ,
        L (graphParamVariation u β a t (φ x))+v =
          L (φ x,u (φ x))+v+t • V x) ∧
      HasDerivAt (fun t : ℝ => ∫ x in K,
        coordinateAffineVariationArea L v φ u β a x t) 0 0 := by
  sorry

end AffineBernstein
end

end OAI
end
