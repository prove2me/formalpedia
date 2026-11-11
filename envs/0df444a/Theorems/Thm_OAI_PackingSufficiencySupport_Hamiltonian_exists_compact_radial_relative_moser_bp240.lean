-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_exists_compact_radial_relative_moser_bp240
-- name    : OAI.PackingSufficiencySupport.Hamiltonian.exists_compact_radial_relative_moser_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:55:08.339836+00:00
-- url     : https://prove2.me/theorems/24168e7f-ce2e-4ef3-a17f-41a32fe5a090
-- title:
--   OAI.PackingSufficiencySupport.Hamiltonian.exists_compact_radial_relative_moser_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.Hamiltonian.exists_compact_radial_relative_moser` of [lean/OAI/Geometry/BallPacking/Moser/ManifoldExteriorNaturality.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Moser/ManifoldExteriorNaturality.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.Hamiltonian`, with `open scoped ContDiff Manifold Topology`, `open Set Function Manifold`, `open MeasureTheory`):
--
--   ```lean
--    theorem exists_compact_radial_relative_moser_bp240
--       {Ω : ℝ → ManifoldTwoForm (PlanePhase ι) (PlanePhase ι)}
--       {α : ℝ → ManifoldOneForm (PlanePhase ι) (PlanePhase ι)}
--       (h : ManifoldMoserData Ω α) {K O : Set (PlanePhase ι)}
--       (hK : IsCompact K) (hO : IsOpen O) (hKO : K⊆O)
--       (hKr : ∀ x∈K,∀ y,phaseSq y=phaseSq x → y∈K)
--       {c : ℝ} (hc : c≠0)
--       (hcircle : ∀ s,∀ z∈O,∀ v,Ω s z v (phaseJ z)=c*phaseDot z v)
--       (hαcircle : ∀ s,∀ z∈O,α s z (phaseJ z)=0)
--       (e : F →L[ℝ] PlanePhase ι) (P : PlanePhase ι →L[ℝ] F)
--       (hPe : P.comp e=ContinuousLinearMap.id ℝ F)
--       (htan : ∀ s∈Icc (0:ℝ) 1,∀ x,e x∈O →
--         e (P (manifoldMoserField Ω α (s,e x)))=manifoldMoserField Ω α (s,e x)) :
--       ∃ Φ Ψ : ℝ × PlanePhase ι → PlanePhase ι,
--         ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ Ψ ∧
--         (∀ x,Φ (0,x)=x) ∧
--         (∀ t∈Icc (0:ℝ) 1,∀ x,Ψ (t,Φ (t,x))=x ∧ Φ (t,Ψ (t,x))=x) ∧
--         (∀ t∈Icc (0:ℝ) 1,∀ x,phaseSq (Φ (t,x))=phaseSq x) ∧
--         (∀ t∈Icc (0:ℝ) 1,(fun x => Φ (t,x)) '' range e=range e) ∧
--         (∀ t∈Icc (0:ℝ) 1,∀ x∈K,∀ v w,manifoldPullback Φ Ω t x v w=Ω 0 x v w)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldTwoForm`, `OAI.PackingSufficiencySupport.Hamiltonian.Plane`, `OAI.PackingSufficiencySupport.Hamiltonian.PlanePhase`, `OAI.PackingSufficiencySupport.Hamiltonian.phaseDot`, `OAI.PackingSufficiencySupport.Hamiltonian.phaseJ` and `OAI.PackingSufficiencySupport.Hamiltonian.phaseSq` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.manifoldMoserField` and `OAI.PackingSufficiencySupport.Hamiltonian.manifoldPullback` (definitions bundle `OAIQ240Bp007` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldMoserData` (definitions bundle `OAIQ240Bp019` of this split).
--
--   **Used by.** The proof of `OAI.PackingSufficiencySupport.Hamiltonian.exists_circle_relative_radial_moser_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Moser/ManifoldExteriorNaturality.lean (declaration OAI.PackingSufficiencySupport.Hamiltonian.exists_compact_radial_relative_moser)

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
open MeasureTheory
section

variable {ι : Type} [Fintype ι]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

 theorem exists_compact_radial_relative_moser_bp240
    {Ω : ℝ → ManifoldTwoForm (PlanePhase ι) (PlanePhase ι)}
    {α : ℝ → ManifoldOneForm (PlanePhase ι) (PlanePhase ι)}
    (h : ManifoldMoserData Ω α) {K O : Set (PlanePhase ι)}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K⊆O)
    (hKr : ∀ x∈K,∀ y,phaseSq y=phaseSq x → y∈K)
    {c : ℝ} (hc : c≠0)
    (hcircle : ∀ s,∀ z∈O,∀ v,Ω s z v (phaseJ z)=c*phaseDot z v)
    (hαcircle : ∀ s,∀ z∈O,α s z (phaseJ z)=0)
    (e : F →L[ℝ] PlanePhase ι) (P : PlanePhase ι →L[ℝ] F)
    (hPe : P.comp e=ContinuousLinearMap.id ℝ F)
    (htan : ∀ s∈Icc (0:ℝ) 1,∀ x,e x∈O →
      e (P (manifoldMoserField Ω α (s,e x)))=manifoldMoserField Ω α (s,e x)) :
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
