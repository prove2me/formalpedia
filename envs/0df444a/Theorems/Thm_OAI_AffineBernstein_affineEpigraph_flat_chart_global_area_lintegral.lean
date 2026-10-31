-- Prove2me | Theorems.Thm_OAI_AffineBernstein_affineEpigraph_flat_chart_global_area_lintegral
-- name    : OAI.AffineBernstein.affineEpigraph_flat_chart_global_area_lintegral
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:03:12.112152+00:00
-- url     : https://prove2.me/theorems/abed9a0b-2a6f-4be0-8c37-43ca77fad62a
-- title:
--   OAI.AffineBernstein.affineEpigraph_flat_chart_global_area_lintegral: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.affineEpigraph_flat_chart_global_area_lintegral` of [lean/OAI/Analysis/AffineBernstein/GlobalFlatAreaLIntegral.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/GlobalFlatAreaLIntegral.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem affineEpigraph_flat_chart_global_area_lintegral {n : ℕ} {Ω : Set (Space n)}
--       (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
--       (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
--       (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
--       {B : Set S} (hB : IsOpen B)
--       (hK : ∀ s ∈ B, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
--       (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
--       (q₀ : S × E) (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
--       (hd : inner ℝ q₀.2 (bE (Sum.inr ())) = 1)
--       (J : Space n →L[ℝ] (S × E)) (hi : Function.Injective J)
--       (hJ : ∀ v, inner ℝ (J v).2 (bE (Sum.inr ())) = 0)
--       (e : Fin n ≃ ι ⊕ κ) (hJe : ∀ i, J (coordinateVector n i) = tubeTangent bS bE (e i))
--       :
--       let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
--       let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
--       let X := fun x : Space n => supportParam Y (q₀+J x)
--       let eA := (Equiv.sumCongr e (Equiv.refl Unit)).trans (Equiv.sumAssoc ι κ Unit)
--       let b := (bS.prod bE.toBasis).reindex eA.symm
--       ∃ φ : OpenPartialHomeomorph (Space n) (Space n),
--         φ.source = {x | (q₀+J x).1 ∈ B} ∧ φ.target ⊆ Ω ∧
--         ContDiffOn ℝ ∞ φ φ.source ∧ ContDiffOn ℝ ∞ φ.symm φ.target ∧
--         (∀ x ∈ φ.source, a+L (X x) = (φ x,u (φ x))) ∧
--         ∀ (K : Set (Space n)), MeasurableSet K → K ⊆ φ.source →
--         ∀ (w : Space n → ℝ≥0∞),
--         (∫⁻ x in K, ENNReal.ofReal (tubeAreaDensity (tubeBaseMatrix H (q₀+J x) bS)
--           (tubeRadiusMatrix H (q₀+J x) bE) (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))) * w (φ x)) =
--           ENNReal.ofReal (Real.rpow |b.det ((graphAmbientBasis n).map L.symm.toLinearEquiv)|
--             ((n : ℝ)/((n : ℝ)+2))) * ∫⁻ y in φ '' K, ENNReal.ofReal (affineAreaDensity u y) * w y
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.affineAreaDensity`, `OAI.AffineBernstein.affineEpigraphPullback`, `OAI.AffineBernstein.gaussPoint`, `OAI.AffineBernstein.graphAmbientBasis`, `OAI.AffineBernstein.homogeneousSupport`, `OAI.AffineBernstein.supportParam`, `OAI.AffineBernstein.tubeAreaDensity`, `OAI.AffineBernstein.tubeBaseMatrix`, `OAI.AffineBernstein.tubeRadiusMatrix` and `OAI.AffineBernstein.tubeTangent` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.Space`, `OAI.AffineBernstein.coordinateVector` and `OAI.AffineBernstein.hessian` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proofs of `OAI.AffineBernstein.affineEpigraph_flat_chart_global_inverseArea_lintegral` and `OAI.AffineBernstein.affineEpigraph_product_area_chart` of this split import it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/GlobalFlatAreaLIntegral.lean (declaration OAI.AffineBernstein.affineEpigraph_flat_chart_global_area_lintegral)

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
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem affineEpigraph_flat_chart_global_area_lintegral {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (q₀ : S × E) (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hd : inner ℝ q₀.2 (bE (Sum.inr ())) = 1)
    (J : Space n →L[ℝ] (S × E)) (hi : Function.Injective J)
    (hJ : ∀ v, inner ℝ (J v).2 (bE (Sum.inr ())) = 0)
    (e : Fin n ≃ ι ⊕ κ) (hJe : ∀ i, J (coordinateVector n i) = tubeTangent bS bE (e i))
    :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let X := fun x : Space n => supportParam Y (q₀+J x)
    let eA := (Equiv.sumCongr e (Equiv.refl Unit)).trans (Equiv.sumAssoc ι κ Unit)
    let b := (bS.prod bE.toBasis).reindex eA.symm
    ∃ φ : OpenPartialHomeomorph (Space n) (Space n),
      φ.source = {x | (q₀+J x).1 ∈ B} ∧ φ.target ⊆ Ω ∧
      ContDiffOn ℝ ∞ φ φ.source ∧ ContDiffOn ℝ ∞ φ.symm φ.target ∧
      (∀ x ∈ φ.source, a+L (X x) = (φ x,u (φ x))) ∧
      ∀ (K : Set (Space n)), MeasurableSet K → K ⊆ φ.source →
      ∀ (w : Space n → ℝ≥0∞),
      (∫⁻ x in K, ENNReal.ofReal (tubeAreaDensity (tubeBaseMatrix H (q₀+J x) bS)
        (tubeRadiusMatrix H (q₀+J x) bE) (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))) * w (φ x)) =
        ENNReal.ofReal (Real.rpow |b.det ((graphAmbientBasis n).map L.symm.toLinearEquiv)|
          ((n : ℝ)/((n : ℝ)+2))) * ∫⁻ y in φ '' K, ENNReal.ofReal (affineAreaDensity u y) * w y := by
  sorry

end AffineBernstein
end

end OAI
end
