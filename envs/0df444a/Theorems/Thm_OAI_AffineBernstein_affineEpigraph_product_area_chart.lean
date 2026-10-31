-- Prove2me | Theorems.Thm_OAI_AffineBernstein_affineEpigraph_product_area_chart
-- name    : OAI.AffineBernstein.affineEpigraph_product_area_chart
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:06:41.580581+00:00
-- url     : https://prove2.me/theorems/376a75e7-0523-45e5-9a48-1d7b9d6ed0bc
-- title:
--   OAI.AffineBernstein.affineEpigraph_product_area_chart: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.affineEpigraph_product_area_chart` of [lean/OAI/Analysis/AffineBernstein/ProductAreaChart.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/ProductAreaChart.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`):
--
--   ```lean
--   theorem affineEpigraph_product_area_chart {n : ℕ} {Ω : Set (Space n)}
--       (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
--       (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
--       (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
--       {D : Set S} (hD : IsOpen D)
--       (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
--       (hzero : ∀ s ∈ D, (0:E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
--       (bS : OrthonormalBasis ι ℝ S) (bF : OrthonormalBasis κ ℝ F)
--       (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (e : Fin n ≃ ι ⊕ κ) :
--       let Z := flatProductCoordinates bS bF e
--       let bE := flatProductFiberBasis bF f
--       let eA := (Equiv.sumCongr e (Equiv.refl Unit)).trans (Equiv.sumAssoc ι κ Unit)
--       let b := (bS.toBasis.prod bE.toBasis).reindex eA.symm
--       let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
--       ∃ φ : OpenPartialHomeomorph (Space n) (Space n),
--         φ.source = {x | (Z x).1 ∈ D} ∧ φ.target ⊆ Ω ∧
--         (∀ x ∈ φ.source, a+L ((Z x).1,
--           gaussPoint {y | ((Z x).1,y) ∈ affineEpigraphPullback Ω u a L}
--             (f (WithLp.toLp 2 ((Z x).2,(1:ℝ))))) = (φ x,u (φ x))) ∧
--         ∀ {Q : Set S}, MeasurableSet Q → Q ⊆ D →
--           ENNReal.ofReal (Real.rpow |b.det ((graphAmbientBasis n).map L.symm.toLinearEquiv)|
--             ((n:ℝ)/((n:ℝ)+2))) *
--             (∫⁻ y in φ '' (Z ⁻¹' (Q ×ˢ Set.univ)), ENNReal.ofReal (affineAreaDensity u y)) =
--           (∫⁻ q : S × F, ENNReal.ofReal (tubeAreaDensity
--             (tubeBaseMatrix H (q.1,f (WithLp.toLp 2 (q.2,(1:ℝ)))) bS.toBasis)
--             (tubeRadiusMatrix H (q.1,f (WithLp.toLp 2 (q.2,(1:ℝ)))) bE)
--             (1/((Fintype.card ι:ℝ)+Fintype.card κ+2))) ∂(volume.restrict Q).prod volume)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.affineAreaDensity`, `OAI.AffineBernstein.affineEpigraphPullback`, `OAI.AffineBernstein.flatProductCoordinates`, `OAI.AffineBernstein.flatProductFiberBasis`, `OAI.AffineBernstein.gaussPoint`, `OAI.AffineBernstein.graphAmbientBasis`, `OAI.AffineBernstein.homogeneousSupport`, `OAI.AffineBernstein.tubeAreaDensity`, `OAI.AffineBernstein.tubeBaseMatrix` and `OAI.AffineBernstein.tubeRadiusMatrix` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.Space` and `OAI.AffineBernstein.hessian` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proof of `OAI.AffineBernstein.affineEpigraph_whole_graph_area_bound` of this split imports it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/ProductAreaChart.lean (declaration OAI.AffineBernstein.affineEpigraph_product_area_chart)

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

section ProductAreaChart
variable {S E F : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem affineEpigraph_product_area_chart {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0:E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bS : OrthonormalBasis ι ℝ S) (bF : OrthonormalBasis κ ℝ F)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (e : Fin n ≃ ι ⊕ κ) :
    let Z := flatProductCoordinates bS bF e
    let bE := flatProductFiberBasis bF f
    let eA := (Equiv.sumCongr e (Equiv.refl Unit)).trans (Equiv.sumAssoc ι κ Unit)
    let b := (bS.toBasis.prod bE.toBasis).reindex eA.symm
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    ∃ φ : OpenPartialHomeomorph (Space n) (Space n),
      φ.source = {x | (Z x).1 ∈ D} ∧ φ.target ⊆ Ω ∧
      (∀ x ∈ φ.source, a+L ((Z x).1,
        gaussPoint {y | ((Z x).1,y) ∈ affineEpigraphPullback Ω u a L}
          (f (WithLp.toLp 2 ((Z x).2,(1:ℝ))))) = (φ x,u (φ x))) ∧
      ∀ {Q : Set S}, MeasurableSet Q → Q ⊆ D →
        ENNReal.ofReal (Real.rpow |b.det ((graphAmbientBasis n).map L.symm.toLinearEquiv)|
          ((n:ℝ)/((n:ℝ)+2))) *
          (∫⁻ y in φ '' (Z ⁻¹' (Q ×ˢ Set.univ)), ENNReal.ofReal (affineAreaDensity u y)) =
        (∫⁻ q : S × F, ENNReal.ofReal (tubeAreaDensity
          (tubeBaseMatrix H (q.1,f (WithLp.toLp 2 (q.2,(1:ℝ)))) bS.toBasis)
          (tubeRadiusMatrix H (q.1,f (WithLp.toLp 2 (q.2,(1:ℝ)))) bE)
          (1/((Fintype.card ι:ℝ)+Fintype.card κ+2))) ∂(volume.restrict Q).prod volume) := by
  sorry

end ProductAreaChart

end
end AffineBernstein
end

end OAI
end
