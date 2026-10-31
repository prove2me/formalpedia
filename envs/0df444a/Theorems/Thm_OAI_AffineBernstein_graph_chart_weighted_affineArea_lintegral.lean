-- Prove2me | Theorems.Thm_OAI_AffineBernstein_graph_chart_weighted_affineArea_lintegral
-- name    : OAI.AffineBernstein.graph_chart_weighted_affineArea_lintegral
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:10:38.493094+00:00
-- url     : https://prove2.me/theorems/1d535d12-9474-488f-9b6e-c485ec13294d
-- title:
--   OAI.AffineBernstein.graph_chart_weighted_affineArea_lintegral: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.graph_chart_weighted_affineArea_lintegral` of [lean/OAI/Analysis/AffineBernstein/WeightedChartLIntegral.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/WeightedChartLIntegral.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem graph_chart_weighted_affineArea_lintegral {E : Type*}
--       [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} {U Ω : Set (Space n)}
--       (hU : IsOpen U) (hΩ : IsOpen Ω) {X : Space n → E} {u : Space n → ℝ}
--       (hX : ContDiffOn ℝ ∞ X U) (hu : ContDiffOn ℝ ∞ u Ω)
--       (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
--       (a : Space n × ℝ) (L : E ≃L[ℝ] (Space n × ℝ))
--       (φ : OpenPartialHomeomorph (Space n) (Space n))
--       (hs : φ.source ⊆ U) (ht : φ.target ⊆ Ω)
--       (hφ : ContDiffOn ℝ ∞ φ φ.source) (hψ : ContDiffOn ℝ ∞ φ.symm φ.target)
--       (he : ∀ x ∈ φ.source, a+L (X x) = (φ x,u (φ x)))
--       (b : Module.Basis (Fin n ⊕ Unit) ℝ E)
--       {K : Set (Space n)} (hK : MeasurableSet K) (hKW : K ⊆ φ.source)
--       (ν : Space n → E →L[ℝ] ℝ) (ξ : Space n → E)
--       (hν : ∀ x ∈ K, (ν x).comp (fderiv ℝ X x) = 0)
--       (hξ : ∀ x ∈ K, ν x (ξ x) = 1)
--       (hc : ∀ x ∈ K, 0 < ν x (L.symm ((0 : Space n),1))) (w : Space n → ℝ≥0∞) :
--       (∫⁻ x in K, ENNReal.ofReal (parametricAreaDensity b X (ν x) (ξ x) x) * w (φ x)) =
--         ENNReal.ofReal (Real.rpow |b.det ((graphAmbientBasis n).map L.symm.toLinearEquiv)|
--           ((n : ℝ)/((n : ℝ)+2))) * ∫⁻ y in φ '' K, ENNReal.ofReal (affineAreaDensity u y) * w y
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.affineAreaDensity`, `OAI.AffineBernstein.graphAmbientBasis` and `OAI.AffineBernstein.parametricAreaDensity` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.Space` and `OAI.AffineBernstein.hessian` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proof of `OAI.AffineBernstein.affineEpigraph_flat_chart_global_area_lintegral` of this split imports it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/WeightedChartLIntegral.lean (declaration OAI.AffineBernstein.graph_chart_weighted_affineArea_lintegral)

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

open Filter
open scoped Topology

theorem graph_chart_weighted_affineArea_lintegral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} {U Ω : Set (Space n)}
    (hU : IsOpen U) (hΩ : IsOpen Ω) {X : Space n → E} {u : Space n → ℝ}
    (hX : ContDiffOn ℝ ∞ X U) (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : E ≃L[ℝ] (Space n × ℝ))
    (φ : OpenPartialHomeomorph (Space n) (Space n))
    (hs : φ.source ⊆ U) (ht : φ.target ⊆ Ω)
    (hφ : ContDiffOn ℝ ∞ φ φ.source) (hψ : ContDiffOn ℝ ∞ φ.symm φ.target)
    (he : ∀ x ∈ φ.source, a+L (X x) = (φ x,u (φ x)))
    (b : Module.Basis (Fin n ⊕ Unit) ℝ E)
    {K : Set (Space n)} (hK : MeasurableSet K) (hKW : K ⊆ φ.source)
    (ν : Space n → E →L[ℝ] ℝ) (ξ : Space n → E)
    (hν : ∀ x ∈ K, (ν x).comp (fderiv ℝ X x) = 0)
    (hξ : ∀ x ∈ K, ν x (ξ x) = 1)
    (hc : ∀ x ∈ K, 0 < ν x (L.symm ((0 : Space n),1))) (w : Space n → ℝ≥0∞) :
    (∫⁻ x in K, ENNReal.ofReal (parametricAreaDensity b X (ν x) (ξ x) x) * w (φ x)) =
      ENNReal.ofReal (Real.rpow |b.det ((graphAmbientBasis n).map L.symm.toLinearEquiv)|
        ((n : ℝ)/((n : ℝ)+2))) * ∫⁻ y in φ '' K, ENNReal.ofReal (affineAreaDensity u y) * w y := by
  sorry

end AffineBernstein
end

end OAI
end
