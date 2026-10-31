-- Prove2me | Theorems.Thm_OAI_AffineBernstein_affineEpigraph_whole_graph_area_bound
-- name    : OAI.AffineBernstein.affineEpigraph_whole_graph_area_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:07:04.661788+00:00
-- url     : https://prove2.me/theorems/ea318369-bcf0-4744-9388-8131be624323
-- title:
--   OAI.AffineBernstein.affineEpigraph_whole_graph_area_bound: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.affineEpigraph_whole_graph_area_bound` of [lean/OAI/Analysis/AffineBernstein/WholeGraphAreaTransport.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/WholeGraphAreaTransport.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`):
--
--   ```lean
--   theorem affineEpigraph_whole_graph_area_bound {n : ℕ}
--       (bS : OrthonormalBasis ι ℝ S) (bF : OrthonormalBasis κ ℝ F)
--       (bRef : OrthonormalBasis (κ ⊕ Unit) ℝ E)
--       (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (e : Fin n ≃ ι ⊕ κ) :
--       ∃ C > 0, ∀ {Ω : Set (Space n)}, IsOpen Ω → Convex ℝ Ω →
--       ∀ {u : Space n → ℝ}, ContDiffOn ℝ ∞ u Ω →
--       (∀ x ∈ Ω, (hessian u x).PosDef) →
--       ∀ (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
--         {D : Set S}, IsOpen D →
--       (∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L}) →
--       (∀ s ∈ D, (0:E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L}) →
--       ∀ {Q : Set S}, MeasurableSet Q → Q ⊆ D →
--       ∀ {K : Set (Space n)}, K ⊆ Ω →
--       (∀ x ∈ K, (L.symm ((x,u x)-a)).1 ∈ Q) →
--       let eA := (Equiv.sumCongr e (Equiv.refl Unit)).trans (Equiv.sumAssoc ι κ Unit)
--       let b := (bS.toBasis.prod bRef.toBasis).reindex eA.symm
--       let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
--       let δ := 1/((Fintype.card ι:ℝ)+Fintype.card κ+2)
--       ENNReal.ofReal (Real.rpow |b.det ((graphAmbientBasis n).map L.symm.toLinearEquiv)|
--         ((n:ℝ)/((n:ℝ)+2))) *
--           (∫⁻ x in K, ENNReal.ofReal (affineAreaDensity u x)) ≤
--       ENNReal.ofReal C * (∫⁻ s in Q, ∫⁻ v : Metric.sphere (0:E) 1,
--         ENNReal.ofReal (Real.rpow (tubeBaseMatrix H (s,v) bS.toBasis).det δ *
--           Real.rpow (tubeAngularDensity H (s,v) bRef) (1-δ)) ∂volume.toSphere)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.affineAreaDensity`, `OAI.AffineBernstein.affineEpigraphPullback`, `OAI.AffineBernstein.graphAmbientBasis`, `OAI.AffineBernstein.homogeneousSupport`, `OAI.AffineBernstein.tubeAngularDensity` and `OAI.AffineBernstein.tubeBaseMatrix` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.Space` and `OAI.AffineBernstein.hessian` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proof of `OAI.AffineBernstein.normalized_model_positive_log_mass` of this split imports it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/WholeGraphAreaTransport.lean (declaration OAI.AffineBernstein.affineEpigraph_whole_graph_area_bound)

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

section WholeGraphAreaTransport
variable {S E F : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem affineEpigraph_whole_graph_area_bound {n : ℕ}
    (bS : OrthonormalBasis ι ℝ S) (bF : OrthonormalBasis κ ℝ F)
    (bRef : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (e : Fin n ≃ ι ⊕ κ) :
    ∃ C > 0, ∀ {Ω : Set (Space n)}, IsOpen Ω → Convex ℝ Ω →
    ∀ {u : Space n → ℝ}, ContDiffOn ℝ ∞ u Ω →
    (∀ x ∈ Ω, (hessian u x).PosDef) →
    ∀ (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
      {D : Set S}, IsOpen D →
    (∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L}) →
    (∀ s ∈ D, (0:E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L}) →
    ∀ {Q : Set S}, MeasurableSet Q → Q ⊆ D →
    ∀ {K : Set (Space n)}, K ⊆ Ω →
    (∀ x ∈ K, (L.symm ((x,u x)-a)).1 ∈ Q) →
    let eA := (Equiv.sumCongr e (Equiv.refl Unit)).trans (Equiv.sumAssoc ι κ Unit)
    let b := (bS.toBasis.prod bRef.toBasis).reindex eA.symm
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let δ := 1/((Fintype.card ι:ℝ)+Fintype.card κ+2)
    ENNReal.ofReal (Real.rpow |b.det ((graphAmbientBasis n).map L.symm.toLinearEquiv)|
      ((n:ℝ)/((n:ℝ)+2))) *
        (∫⁻ x in K, ENNReal.ofReal (affineAreaDensity u x)) ≤
    ENNReal.ofReal C * (∫⁻ s in Q, ∫⁻ v : Metric.sphere (0:E) 1,
      ENNReal.ofReal (Real.rpow (tubeBaseMatrix H (s,v) bS.toBasis).det δ *
        Real.rpow (tubeAngularDensity H (s,v) bRef) (1-δ)) ∂volume.toSphere) := by
  sorry
end WholeGraphAreaTransport

end
end AffineBernstein
end

end OAI
end
