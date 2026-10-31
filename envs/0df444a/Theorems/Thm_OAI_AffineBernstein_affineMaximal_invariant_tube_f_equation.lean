-- Prove2me | Theorems.Thm_OAI_AffineBernstein_affineMaximal_invariant_tube_f_equation
-- name    : OAI.AffineBernstein.affineMaximal_invariant_tube_f_equation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:07:55.017777+00:00
-- url     : https://prove2.me/theorems/d2132c16-c8b2-4efe-9a38-1d4b6aabcd35
-- title:
--   OAI.AffineBernstein.affineMaximal_invariant_tube_f_equation: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.affineMaximal_invariant_tube_f_equation` of [lean/OAI/Analysis/AffineBernstein/ActualAmbientFEquation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/ActualAmbientFEquation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem affineMaximal_invariant_tube_f_equation {n : ℕ} {Ω : Set (Space n)}
--       (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
--       (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
--       (hm : AffineMaximalOn Ω u)
--       (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
--       {D : Set S} (hD : IsOpen D)
--       (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
--       (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
--       {s : S} (hs : s ∈ D) {e : E}
--       (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
--       (he : bE (Sum.inr ()) = e) :
--       let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
--       let q := (s,e)
--       let B := tubeBaseMatrix H q bS
--       let R := tubeRadiusMatrix H q bE
--       let V := fun i : ι => ((bS i), (0:E))
--       let W := fun i : κ => ((0:S), bE (Sum.inl i))
--       let δ : ℝ := 1/((Fintype.card ι : ℝ)+Fintype.card κ+2)
--       let F := invariantTubeF H bS bE δ
--       let P := fun y => Real.log (H y)
--       let T := fun y => F y+P y
--       (n : ℝ) - 2*Fintype.card ι + H q*flatInverseTrace B V F q -
--         H q*flatInversePair B V P P q -
--         ((n : ℝ)+1)*H q*flatInversePair B V T T q +
--         H q*flatInverseTrace R W F q + 2*H q*flatInversePair R W P F q +
--         H q*flatInversePair R W F F q = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.affineEpigraphPullback`, `OAI.AffineBernstein.flatInversePair`, `OAI.AffineBernstein.flatInverseTrace`, `OAI.AffineBernstein.homogeneousSupport`, `OAI.AffineBernstein.invariantTubeF`, `OAI.AffineBernstein.tubeBaseMatrix` and `OAI.AffineBernstein.tubeRadiusMatrix` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.AffineMaximalOn`, `OAI.AffineBernstein.Space` and `OAI.AffineBernstein.hessian` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proof of `OAI.AffineBernstein.affineMaximal_round_tube_f_equation` of this split imports it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/ActualAmbientFEquation.lean (declaration OAI.AffineBernstein.affineMaximal_invariant_tube_f_equation)

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

theorem affineMaximal_invariant_tube_f_equation {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D) {e : E}
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (he : bE (Sum.inr ()) = e) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let q := (s,e)
    let B := tubeBaseMatrix H q bS
    let R := tubeRadiusMatrix H q bE
    let V := fun i : ι => ((bS i), (0:E))
    let W := fun i : κ => ((0:S), bE (Sum.inl i))
    let δ : ℝ := 1/((Fintype.card ι : ℝ)+Fintype.card κ+2)
    let F := invariantTubeF H bS bE δ
    let P := fun y => Real.log (H y)
    let T := fun y => F y+P y
    (n : ℝ) - 2*Fintype.card ι + H q*flatInverseTrace B V F q -
      H q*flatInversePair B V P P q -
      ((n : ℝ)+1)*H q*flatInversePair B V T T q +
      H q*flatInverseTrace R W F q + 2*H q*flatInversePair R W P F q +
      H q*flatInversePair R W F F q = 0 := by
  sorry

end AffineBernstein
end

end OAI
end
