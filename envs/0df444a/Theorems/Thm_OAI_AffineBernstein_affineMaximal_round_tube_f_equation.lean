-- Prove2me | Theorems.Thm_OAI_AffineBernstein_affineMaximal_round_tube_f_equation
-- name    : OAI.AffineBernstein.affineMaximal_round_tube_f_equation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:08:45.216704+00:00
-- url     : https://prove2.me/theorems/1e25e862-7b33-43e7-a2f3-a0b0efb22ba5
-- title:
--   OAI.AffineBernstein.affineMaximal_round_tube_f_equation: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.affineMaximal_round_tube_f_equation` of [lean/OAI/Analysis/AffineBernstein/ActualRoundFEquation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/ActualRoundFEquation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`):
--
--   ```lean
--   theorem affineMaximal_round_tube_f_equation {n : ℕ} {Ω : Set (Space n)}
--       (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
--       (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
--       (hm : AffineMaximalOn Ω u)
--       (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
--       {D : Set S} (hD : IsOpen D)
--       (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
--       (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
--       {s : S} (hs : s ∈ D) {e : E} (he : ‖e‖ = 1)
--       (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
--       let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
--       let q := (s,e)
--       let B := tubeBaseMatrix H q bS
--       let Q := tubeAngularDensity H q bE
--       let V := fun i : ι => ((bS i), (0:E))
--       let δ : ℝ := 1/((Fintype.card ι : ℝ)+Fintype.card κ+2)
--       let F := invariantTubeF H bS bE δ
--       let P := fun y => Real.log (H y)
--       let T := fun y => F y+P y
--       let N := supportNewtonTensor bE (fun y => H (s,y))
--       let dF := tangentProjection e (gradient (fun y => F (s,y)) e)
--       let dP := tangentProjection e (gradient (fun y => P (s,y)) e)
--       (n : ℝ) - 2*Fintype.card ι + H q*flatInverseTrace B V F q -
--         H q*flatInversePair B V P P q -
--         ((n : ℝ)+1)*H q*flatInversePair B V T T q +
--         H q/Q * roundHessianContraction bE N (fun y => F (s,y)) e +
--         2*H q/Q * N e dP dF + H q/Q * N e dF dF = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.affineEpigraphPullback`, `OAI.AffineBernstein.flatInversePair`, `OAI.AffineBernstein.flatInverseTrace`, `OAI.AffineBernstein.homogeneousSupport`, `OAI.AffineBernstein.invariantTubeF`, `OAI.AffineBernstein.roundHessianContraction`, `OAI.AffineBernstein.supportNewtonTensor`, `OAI.AffineBernstein.tangentProjection`, `OAI.AffineBernstein.tubeAngularDensity` and `OAI.AffineBernstein.tubeBaseMatrix` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.AffineMaximalOn`, `OAI.AffineBernstein.Space` and `OAI.AffineBernstein.hessian` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proof of `OAI.AffineBernstein.affineMaximal_global_d_identity` of this split imports it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/ActualRoundFEquation.lean (declaration OAI.AffineBernstein.affineMaximal_round_tube_f_equation)

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

variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem affineMaximal_round_tube_f_equation {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D) {e : E} (he : ‖e‖ = 1)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let q := (s,e)
    let B := tubeBaseMatrix H q bS
    let Q := tubeAngularDensity H q bE
    let V := fun i : ι => ((bS i), (0:E))
    let δ : ℝ := 1/((Fintype.card ι : ℝ)+Fintype.card κ+2)
    let F := invariantTubeF H bS bE δ
    let P := fun y => Real.log (H y)
    let T := fun y => F y+P y
    let N := supportNewtonTensor bE (fun y => H (s,y))
    let dF := tangentProjection e (gradient (fun y => F (s,y)) e)
    let dP := tangentProjection e (gradient (fun y => P (s,y)) e)
    (n : ℝ) - 2*Fintype.card ι + H q*flatInverseTrace B V F q -
      H q*flatInversePair B V P P q -
      ((n : ℝ)+1)*H q*flatInversePair B V T T q +
      H q/Q * roundHessianContraction bE N (fun y => F (s,y)) e +
      2*H q/Q * N e dP dF + H q/Q * N e dF dF = 0 := by
  sorry

end AffineBernstein
end

end OAI
end
