-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_exists_compact_radial_exact_moser_bp240
-- name    : OAI.PackingSufficiencySupport.Hamiltonian.exists_compact_radial_exact_moser_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:55:59.690855+00:00
-- url     : https://prove2.me/theorems/9e8ce907-4f83-4b33-bd58-2444fdc66808
-- title:
--   OAI.PackingSufficiencySupport.Hamiltonian.exists_compact_radial_exact_moser_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.Hamiltonian.exists_compact_radial_exact_moser` of [lean/OAI/Geometry/BallPacking/Normal/CompactUniformCentral.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Normal/CompactUniformCentral.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.Hamiltonian`, with `open scoped ContDiff`, `open Set Function`, `open scoped Manifold Topology`, `open Manifold`):
--
--   ```lean
--    theorem exists_compact_radial_exact_moser_bp240
--       {Γ : ℝ → ManifoldOneForm (PlanePhase ι) (PlanePhase ι)}
--       (hΓ : SmoothOneFormFamily Γ) {K O : Set (PlanePhase ι)}
--       (hK : IsCompact K) (hO : IsOpen O) (hKO : K⊆O)
--       (hKr : ∀ x∈K,∀ y,phaseSq y=phaseSq x → y∈K)
--       {c : ℝ} (hc : c≠0)
--       (hcircle : ∀ s,∀ z∈O,∀ v,
--         manifoldExteriorOneForm (Γ s) z v (phaseJ z)=c*phaseDot z v)
--       (hβcircle : ∀ s,∀ z∈O,manifoldTimePrimitive Γ s z (phaseJ z)=0)
--       (hinv : ∀ s∈Icc (0:ℝ) 1,∀ z∈K,(manifoldExteriorOneForm (Γ s) z).IsInvertible) :
--       ∃ Φ Ψ : ℝ × PlanePhase ι → PlanePhase ι,
--         ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ Ψ ∧
--         (∀ x,Φ (0,x)=x) ∧
--         (∀ t∈Icc (0:ℝ) 1,∀ x,Ψ (t,Φ (t,x))=x ∧ Φ (t,Ψ (t,x))=x) ∧
--         (∀ t∈Icc (0:ℝ) 1,∀ x,phaseSq (Φ (t,x))=phaseSq x) ∧
--         (∀ t∈Icc (0:ℝ) 1,∀ x∈K,∀ v w,
--           manifoldPullback Φ (fun s => manifoldExteriorOneForm (Γ s)) t x v w=
--             manifoldExteriorOneForm (Γ 0) x v w) ∧
--         ∃ V : ℝ × PlanePhase ι → PlanePhase ι,
--           ContDiff ℝ ∞ V ∧
--           (∀ x t,t∈Ioo (-2:ℝ) 2 → HasDerivAt (fun s => Φ (s,x)) (V (t,Φ (t,x))) t) ∧
--           ∀ s∈Icc (0:ℝ) 1,∀ x∈K,
--             V (s,x)=manifoldMoserField (fun t => manifoldExteriorOneForm (Γ t)) (manifoldTimePrimitive Γ) (s,x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.Plane`, `OAI.PackingSufficiencySupport.Hamiltonian.PlanePhase`, `OAI.PackingSufficiencySupport.Hamiltonian.SmoothOneFormFamily`, `OAI.PackingSufficiencySupport.Hamiltonian.manifoldExteriorOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.phaseDot`, `OAI.PackingSufficiencySupport.Hamiltonian.phaseJ` and `OAI.PackingSufficiencySupport.Hamiltonian.phaseSq` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.manifoldMoserField` and `OAI.PackingSufficiencySupport.Hamiltonian.manifoldPullback` (definitions bundle `OAIQ240Bp007` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.manifoldTimePrimitive` (definitions bundle `OAIQ240Bp010` of this split).
--
--   **Used by.** The proof of `OAI.PackingSufficiencySupport.DiagonalQuadrics.exists_quadric_relative_shell_map_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Normal/CompactUniformCentral.lean (declaration OAI.PackingSufficiencySupport.Hamiltonian.exists_compact_radial_exact_moser)

import Mathlib
import Definitions.Def_OAIQ240Bp010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Set Function
open scoped Manifold Topology
open Manifold

variable {ι : Type*} [Fintype ι]

 theorem exists_compact_radial_exact_moser_bp240
    {Γ : ℝ → ManifoldOneForm (PlanePhase ι) (PlanePhase ι)}
    (hΓ : SmoothOneFormFamily Γ) {K O : Set (PlanePhase ι)}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K⊆O)
    (hKr : ∀ x∈K,∀ y,phaseSq y=phaseSq x → y∈K)
    {c : ℝ} (hc : c≠0)
    (hcircle : ∀ s,∀ z∈O,∀ v,
      manifoldExteriorOneForm (Γ s) z v (phaseJ z)=c*phaseDot z v)
    (hβcircle : ∀ s,∀ z∈O,manifoldTimePrimitive Γ s z (phaseJ z)=0)
    (hinv : ∀ s∈Icc (0:ℝ) 1,∀ z∈K,(manifoldExteriorOneForm (Γ s) z).IsInvertible) :
    ∃ Φ Ψ : ℝ × PlanePhase ι → PlanePhase ι,
      ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ Ψ ∧
      (∀ x,Φ (0,x)=x) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x,Ψ (t,Φ (t,x))=x ∧ Φ (t,Ψ (t,x))=x) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x,phaseSq (Φ (t,x))=phaseSq x) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x∈K,∀ v w,
        manifoldPullback Φ (fun s => manifoldExteriorOneForm (Γ s)) t x v w=
          manifoldExteriorOneForm (Γ 0) x v w) ∧
      ∃ V : ℝ × PlanePhase ι → PlanePhase ι,
        ContDiff ℝ ∞ V ∧
        (∀ x t,t∈Ioo (-2:ℝ) 2 → HasDerivAt (fun s => Φ (s,x)) (V (t,Φ (t,x))) t) ∧
        ∀ s∈Icc (0:ℝ) 1,∀ x∈K,
          V (s,x)=manifoldMoserField (fun t => manifoldExteriorOneForm (Γ t)) (manifoldTimePrimitive Γ) (s,x) := by
  sorry

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end
