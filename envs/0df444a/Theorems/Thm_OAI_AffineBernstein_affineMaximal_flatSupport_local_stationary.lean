-- Prove2me | Theorems.Thm_OAI_AffineBernstein_affineMaximal_flatSupport_local_stationary
-- name    : OAI.AffineBernstein.affineMaximal_flatSupport_local_stationary
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:07:39.341262+00:00
-- url     : https://prove2.me/theorems/fd65be0e-0c68-459d-84c7-8dfb282add15
-- title:
--   OAI.AffineBernstein.affineMaximal_flatSupport_local_stationary: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.affineMaximal_flatSupport_local_stationary` of [lean/OAI/Analysis/AffineBernstein/ParametricBasis.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/ParametricBasis.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem affineMaximal_flatSupport_local_stationary {n : ℕ} {Ω : Set (Space n)}
--       (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
--       (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
--       (hm : AffineMaximalOn Ω u)
--       (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
--       {B : Set S} (hB : IsOpen B)
--       (hK : ∀ s ∈ B, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
--       (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
--       (q₀ : S × E) (d : E) (hd : inner ℝ q₀.2 d = 1)
--       (J : Space n →L[ℝ] (S × E)) (hi : Function.Injective J)
--       (hJ : ∀ v, inner ℝ (J v).2 d = 0)
--       (b : Module.Basis (Fin n ⊕ Unit) ℝ (S × E))
--       {x₀ : Space n} (hx₀ : (q₀+J x₀).1 ∈ B) :
--       let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
--       let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
--       let X := fun x : Space n => supportParam Y (q₀+J x)
--       ∃ W : Set (Space n), IsOpen W ∧ x₀ ∈ W ∧ W ⊆ {x | (q₀+J x).1 ∈ B} ∧
--         ∀ (K : Set (Space n)), IsCompact K → K ⊆ W →
--         ∀ (V : Space n → S × E), ContDiffOn ℝ ∞ V W → tsupport V ⊆ K →
--         ∀ (ν : ℝ → Space n → (S × E) →L[ℝ] ℝ) (ξ : ℝ → Space n → S × E),
--         (∀ t x, x ∈ W → (ν t x).comp (fderiv ℝ (fun y => X y+t • V y) x) = 0) →
--         (∀ t x, x ∈ W → ν t x (ξ t x) = 1) →
--         (∀ x ∈ K, ν 0 x = supportConormal H (q₀+J x)) →
--         (∀ x ∈ K, ContinuousAt (fun q : ℝ × Space n => ν q.1 q.2 (L.symm ((0 : Space n),1))) (0,x)) →
--         HasDerivAt (fun t : ℝ => ∫ x in K, parametricAreaDensity b
--           (fun y => X y+t • V y) (ν t x) (ξ t x) x) 0 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.affineEpigraphPullback`, `OAI.AffineBernstein.gaussPoint`, `OAI.AffineBernstein.homogeneousSupport`, `OAI.AffineBernstein.parametricAreaDensity`, `OAI.AffineBernstein.supportConormal` and `OAI.AffineBernstein.supportParam` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.AffineMaximalOn`, `OAI.AffineBernstein.Space` and `OAI.AffineBernstein.hessian` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proof of `OAI.AffineBernstein.affineMaximal_flat_tube_weak_euler` of this split imports it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/ParametricBasis.lean (declaration OAI.AffineBernstein.affineMaximal_flatSupport_local_stationary)

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

theorem affineMaximal_flatSupport_local_stationary {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (q₀ : S × E) (d : E) (hd : inner ℝ q₀.2 d = 1)
    (J : Space n →L[ℝ] (S × E)) (hi : Function.Injective J)
    (hJ : ∀ v, inner ℝ (J v).2 d = 0)
    (b : Module.Basis (Fin n ⊕ Unit) ℝ (S × E))
    {x₀ : Space n} (hx₀ : (q₀+J x₀).1 ∈ B) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let X := fun x : Space n => supportParam Y (q₀+J x)
    ∃ W : Set (Space n), IsOpen W ∧ x₀ ∈ W ∧ W ⊆ {x | (q₀+J x).1 ∈ B} ∧
      ∀ (K : Set (Space n)), IsCompact K → K ⊆ W →
      ∀ (V : Space n → S × E), ContDiffOn ℝ ∞ V W → tsupport V ⊆ K →
      ∀ (ν : ℝ → Space n → (S × E) →L[ℝ] ℝ) (ξ : ℝ → Space n → S × E),
      (∀ t x, x ∈ W → (ν t x).comp (fderiv ℝ (fun y => X y+t • V y) x) = 0) →
      (∀ t x, x ∈ W → ν t x (ξ t x) = 1) →
      (∀ x ∈ K, ν 0 x = supportConormal H (q₀+J x)) →
      (∀ x ∈ K, ContinuousAt (fun q : ℝ × Space n => ν q.1 q.2 (L.symm ((0 : Space n),1))) (0,x)) →
      HasDerivAt (fun t : ℝ => ∫ x in K, parametricAreaDensity b
        (fun y => X y+t • V y) (ν t x) (ξ t x) x) 0 0 := by
  sorry

end AffineBernstein
end

end OAI
end
