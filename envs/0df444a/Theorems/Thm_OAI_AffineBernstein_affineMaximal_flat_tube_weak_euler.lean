-- Prove2me | Theorems.Thm_OAI_AffineBernstein_affineMaximal_flat_tube_weak_euler
-- name    : OAI.AffineBernstein.affineMaximal_flat_tube_weak_euler
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:07:58.041172+00:00
-- url     : https://prove2.me/theorems/127ab398-fbcb-437b-9933-bc98c4a5d512
-- title:
--   OAI.AffineBernstein.affineMaximal_flat_tube_weak_euler: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.affineMaximal_flat_tube_weak_euler` of [lean/OAI/Analysis/AffineBernstein/ActualFlatWeakEuler.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/ActualFlatWeakEuler.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem affineMaximal_flat_tube_weak_euler {n : ℕ} {Ω : Set (Space n)}
--       (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
--       (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
--       (hm : AffineMaximalOn Ω u)
--       (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
--       {B : Set S} (hB : IsOpen B)
--       (hK : ∀ s ∈ B, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
--       (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
--       (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
--       (q₀ : S × E) (hd : inner ℝ q₀.2 (bE (Sum.inr ())) = 1)
--       (J : Space n →L[ℝ] (S × E)) (hi : Function.Injective J)
--       (hJ : ∀ v, inner ℝ (J v).2 (bE (Sum.inr ())) = 0)
--       (C : (S × E) →L[ℝ] Space n) (hC : ∀ x, C (J x) = x)
--       (e : Fin n ≃ ι ⊕ κ)
--       (hJb : ∀ i, J (coordinateVector n i) = tubeTangent bS bE (e i))
--       {x₀ : Space n} (hx₀ : (q₀+J x₀).1 ∈ B) :
--       let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
--       let ℓ := InnerProductSpace.toDual ℝ E (bE (Sum.inr ()))
--       let δ := 1/((Fintype.card ι : ℝ)+Fintype.card κ+2)
--       ∃ W : Set (Space n), IsOpen W ∧ x₀ ∈ W ∧ W ⊆ {x | (q₀+J x).1 ∈ B} ∧
--         ∀ (K : Set (Space n)), IsCompact K → K ⊆ W →
--         ∀ (η : Space n → ℝ), ContDiff ℝ ∞ η → tsupport η ⊆ K →
--         let G := flatSupportVariation ℓ q₀ C η
--         (∫ x in K, tubeAreaFirstVariation (tubeBaseMatrix H (q₀+J x) bS)
--           (tubeBaseMatrix G (q₀+J x) bS) (tubeRadiusMatrix H (q₀+J x) bE)
--           (tubeRadiusMatrix G (q₀+J x) bE) δ) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.affineEpigraphPullback`, `OAI.AffineBernstein.flatSupportVariation`, `OAI.AffineBernstein.homogeneousSupport`, `OAI.AffineBernstein.tubeAreaFirstVariation`, `OAI.AffineBernstein.tubeBaseMatrix`, `OAI.AffineBernstein.tubeRadiusMatrix` and `OAI.AffineBernstein.tubeTangent` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.AffineMaximalOn`, `OAI.AffineBernstein.Space`, `OAI.AffineBernstein.coordinateVector` and `OAI.AffineBernstein.hessian` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proof of `OAI.AffineBernstein.affineMaximal_invariant_tube_f_equation` of this split imports it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/ActualFlatWeakEuler.lean (declaration OAI.AffineBernstein.affineMaximal_flat_tube_weak_euler)

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

theorem affineMaximal_flat_tube_weak_euler {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (q₀ : S × E) (hd : inner ℝ q₀.2 (bE (Sum.inr ())) = 1)
    (J : Space n →L[ℝ] (S × E)) (hi : Function.Injective J)
    (hJ : ∀ v, inner ℝ (J v).2 (bE (Sum.inr ())) = 0)
    (C : (S × E) →L[ℝ] Space n) (hC : ∀ x, C (J x) = x)
    (e : Fin n ≃ ι ⊕ κ)
    (hJb : ∀ i, J (coordinateVector n i) = tubeTangent bS bE (e i))
    {x₀ : Space n} (hx₀ : (q₀+J x₀).1 ∈ B) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let ℓ := InnerProductSpace.toDual ℝ E (bE (Sum.inr ()))
    let δ := 1/((Fintype.card ι : ℝ)+Fintype.card κ+2)
    ∃ W : Set (Space n), IsOpen W ∧ x₀ ∈ W ∧ W ⊆ {x | (q₀+J x).1 ∈ B} ∧
      ∀ (K : Set (Space n)), IsCompact K → K ⊆ W →
      ∀ (η : Space n → ℝ), ContDiff ℝ ∞ η → tsupport η ⊆ K →
      let G := flatSupportVariation ℓ q₀ C η
      (∫ x in K, tubeAreaFirstVariation (tubeBaseMatrix H (q₀+J x) bS)
        (tubeBaseMatrix G (q₀+J x) bS) (tubeRadiusMatrix H (q₀+J x) bE)
        (tubeRadiusMatrix G (q₀+J x) bE) δ) = 0 := by
  sorry

end AffineBernstein
end

end OAI
end
