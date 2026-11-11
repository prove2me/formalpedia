-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_exists_circle_relative_radial_moser_bp240
-- name    : OAI.PackingSufficiencySupport.Hamiltonian.exists_circle_relative_radial_moser_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:55:14.533052+00:00
-- url     : https://prove2.me/theorems/606ab596-b743-4189-87df-adaf95559c47
-- title:
--   OAI.PackingSufficiencySupport.Hamiltonian.exists_circle_relative_radial_moser_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.Hamiltonian.exists_circle_relative_radial_moser` of [lean/OAI/Geometry/BallPacking/CircleAction/CircleRelativeRadialMoser.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/CircleAction/CircleRelativeRadialMoser.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.Hamiltonian`, with `open scoped ContDiff Manifold Topology`, `open Set Function Manifold`, `open scoped BigOperators`):
--
--   ```lean
--    theorem exists_circle_relative_radial_moser_bp240
--       {Ω : ℝ → ManifoldTwoForm (PlanePhase ι) (PlanePhase ι)}
--       {α : ℝ → ManifoldOneForm (PlanePhase ι) (PlanePhase ι)}
--       (h : ManifoldMoserData Ω α)
--       (A : SmoothCircleAction (PlanePhase ι) (PlanePhase ι)) (B : SmoothCircleAction F F)
--       {lam : ℝ} (hlam : lam≠0) (hgen : ∀ z,A.generator z=lam•phaseJ z)
--       (e : F →L[ℝ] PlanePhase ι) (P : PlanePhase ι →L[ℝ] F)
--       (hPe : P.comp e=ContinuousLinearMap.id ℝ F)
--       (he : IsSmoothEmbedding 𝓘(ℝ,F) 𝓘(ℝ,PlanePhase ι) ∞ e)
--       (heq : ∀ s b,e (B.slice s b)=A.slice s (e b))
--       (hΩ : ∀ s t z,(Ω t (A.slice s z)).bilinearComp (A.differential s z) (A.differential s z)=Ω t z)
--       (hi : ∀ t∈Icc (0:ℝ) 1,∀ b,((Ω t (e b)).bilinearComp e e).IsInvertible)
--       {K O : Set (PlanePhase ι)} (hK : IsCompact K) (hO : IsOpen O) (hKO : K⊆O)
--       (hKr : ∀ x∈K,∀ y,phaseSq y=phaseSq x → y∈K)
--       {c : ℝ} (hc : c≠0)
--       (hcircle : ∀ s,∀ z∈O,∀ v,Ω s z v (phaseJ z)=c*phaseDot z v)
--       (ha : ∀ s z,α s z (phaseJ z)=0) :
--       ∃ Φ Ψ : ℝ × PlanePhase ι → PlanePhase ι,
--         ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ Ψ ∧
--         (∀ x,Φ (0,x)=x) ∧
--         (∀ t∈Icc (0:ℝ) 1,∀ x,Ψ (t,Φ (t,x))=x ∧ Φ (t,Ψ (t,x))=x) ∧
--         (∀ t∈Icc (0:ℝ) 1,∀ x,phaseSq (Φ (t,x))=phaseSq x) ∧
--         (∀ t∈Icc (0:ℝ) 1,(fun x => Φ (t,x)) '' range e=range e) ∧
--         (∀ t∈Icc (0:ℝ) 1,∀ x∈K,∀ v w,manifoldPullback Φ Ω t x v w=Ω 0 x v w)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldTwoForm`, `OAI.PackingSufficiencySupport.Hamiltonian.Plane`, `OAI.PackingSufficiencySupport.Hamiltonian.PlanePhase`, `OAI.PackingSufficiencySupport.Hamiltonian.phaseDot`, `OAI.PackingSufficiencySupport.Hamiltonian.phaseJ` and `OAI.PackingSufficiencySupport.Hamiltonian.phaseSq` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.SmoothCircleAction` and `OAI.PackingSufficiencySupport.Hamiltonian.SmoothCircleAction.slice` (definitions bundle `OAIQ240Bp004` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.manifoldPullback`, `OAI.PackingSufficiencySupport.Hamiltonian.SmoothCircleAction.differential` and `OAI.PackingSufficiencySupport.Hamiltonian.SmoothCircleAction.generator` (definitions bundle `OAIQ240Bp007` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldMoserData` (definitions bundle `OAIQ240Bp019` of this split).
--
--   **Used by.** The proof of `OAI.PackingSufficiencySupport.Hamiltonian.exists_degree_relative_shell_maps_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/CircleAction/CircleRelativeRadialMoser.lean (declaration OAI.PackingSufficiencySupport.Hamiltonian.exists_circle_relative_radial_moser)

import Mathlib
import Definitions.Def_OAIQ240Bp019

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
open scoped BigOperators
section

variable {ι : Type} [Fintype ι]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

 theorem exists_circle_relative_radial_moser_bp240
    {Ω : ℝ → ManifoldTwoForm (PlanePhase ι) (PlanePhase ι)}
    {α : ℝ → ManifoldOneForm (PlanePhase ι) (PlanePhase ι)}
    (h : ManifoldMoserData Ω α)
    (A : SmoothCircleAction (PlanePhase ι) (PlanePhase ι)) (B : SmoothCircleAction F F)
    {lam : ℝ} (hlam : lam≠0) (hgen : ∀ z,A.generator z=lam•phaseJ z)
    (e : F →L[ℝ] PlanePhase ι) (P : PlanePhase ι →L[ℝ] F)
    (hPe : P.comp e=ContinuousLinearMap.id ℝ F)
    (he : IsSmoothEmbedding 𝓘(ℝ,F) 𝓘(ℝ,PlanePhase ι) ∞ e)
    (heq : ∀ s b,e (B.slice s b)=A.slice s (e b))
    (hΩ : ∀ s t z,(Ω t (A.slice s z)).bilinearComp (A.differential s z) (A.differential s z)=Ω t z)
    (hi : ∀ t∈Icc (0:ℝ) 1,∀ b,((Ω t (e b)).bilinearComp e e).IsInvertible)
    {K O : Set (PlanePhase ι)} (hK : IsCompact K) (hO : IsOpen O) (hKO : K⊆O)
    (hKr : ∀ x∈K,∀ y,phaseSq y=phaseSq x → y∈K)
    {c : ℝ} (hc : c≠0)
    (hcircle : ∀ s,∀ z∈O,∀ v,Ω s z v (phaseJ z)=c*phaseDot z v)
    (ha : ∀ s z,α s z (phaseJ z)=0) :
    ∃ Φ Ψ : ℝ × PlanePhase ι → PlanePhase ι,
      ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ Ψ ∧
      (∀ x,Φ (0,x)=x) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x,Ψ (t,Φ (t,x))=x ∧ Φ (t,Ψ (t,x))=x) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x,phaseSq (Φ (t,x))=phaseSq x) ∧
      (∀ t∈Icc (0:ℝ) 1,(fun x => Φ (t,x)) '' range e=range e) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x∈K,∀ v w,manifoldPullback Φ Ω t x v w=Ω 0 x v w) := by
  sorry

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end
