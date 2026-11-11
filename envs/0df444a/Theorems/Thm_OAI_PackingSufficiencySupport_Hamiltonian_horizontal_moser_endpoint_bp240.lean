-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_horizontal_moser_endpoint_bp240
-- name    : OAI.PackingSufficiencySupport.Hamiltonian.horizontal_moser_endpoint_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:54:13.239506+00:00
-- url     : https://prove2.me/theorems/11fd6681-497d-4c60-b8bd-9f85f97af529
-- title:
--   OAI.PackingSufficiencySupport.Hamiltonian.horizontal_moser_endpoint_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.Hamiltonian.horizontal_moser_endpoint` of [lean/OAI/Geometry/BallPacking/Toric/StationaryManifoldPullback.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Toric/StationaryManifoldPullback.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.Hamiltonian`, with `open scoped ContDiff Manifold Topology`, `open Set Function Manifold`):
--
--   ```lean
--    theorem horizontal_moser_endpoint_bp240
--       {Ω : V →L[ℝ] V →L[ℝ] ℝ} (hΩ : Ω.IsInvertible) (hs : ∀ u v,Ω u v= -Ω v u)
--       {Γ : ℝ × V → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
--       {D S : Set M} (hS : IsCompact S) (hSD : S⊆interior D)
--       (hstation : ∀ x,x∉S→∀ t v,Γ (t,v) x=Γ (0,v) x)
--       {ι : Type*} (μ : ι → V → ℝ) (hμ : ∀ i,ContDiff ℝ ∞ (μ i))
--       (a c : ι → ℝ) (hac : ∀ i,a i < c i)
--       (hY : IsCompact {v | ∀ i,μ i v ≤ c i})
--       (hInv : ∀ i t x,CollarInvariant Ω (μ i) (a i) (fun v => Γ (t,v) x))
--       (hnon : ∀ t∈Icc (0:ℝ) 1,∀ z∈D ×ˢ {v | ∀ i,μ i v ≤ c i},
--         (globalHorizontalCoupling Ω (fun v => Γ (t,v)) z).IsInvertible) :
--       ∃ e : (M × V) ≃ₘ⟮𝓘(ℝ,E × V),𝓘(ℝ,E × V)⟯ (M × V),
--         e '' (D ×ˢ {v | ∀ i,μ i v ≤ c i})=D ×ˢ {v | ∀ i,μ i v ≤ c i} ∧
--         e '' interior (D ×ˢ {v | ∀ i,μ i v ≤ c i})=interior (D ×ˢ {v | ∀ i,μ i v ≤ c i}) ∧
--         PreservesTwoFormOn e (globalHorizontalCoupling Ω (fun v => Γ (0,v)))
--           (globalHorizontalCoupling Ω (fun v => Γ (1,v))) (D ×ˢ {v | ∀ i,μ i v ≤ c i}) ∧
--         (∃ C : Set (M × V),IsCompact C ∧ ∀ z,z∉C→e z=z) ∧
--         (∀ z,z.1∉S→e z=z)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.Hamiltonian.CollarInvariant`, `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.SmoothOneFormFamily` and `OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.PreservesTwoFormOn` (definitions bundle `OAIQ240Bp007` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.globalHorizontalCoupling` (definitions bundle `OAIQ240Bp010` of this split).
--
--   **Used by.** The proofs of `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.exists_surface_normal_form_packing_bp240`, `OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPath_moser_endpoint_bp240` and `OAI.PackingSufficiencySupport.MomentPolytope.Annular.exhausted_surface_packing_bp240` of this split import it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Toric/StationaryManifoldPullback.lean (declaration OAI.PackingSufficiencySupport.Hamiltonian.horizontal_moser_endpoint)

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
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {M : Type*} [TopologicalSpace M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

 theorem horizontal_moser_endpoint_bp240
    {Ω : V →L[ℝ] V →L[ℝ] ℝ} (hΩ : Ω.IsInvertible) (hs : ∀ u v,Ω u v= -Ω v u)
    {Γ : ℝ × V → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
    {D S : Set M} (hS : IsCompact S) (hSD : S⊆interior D)
    (hstation : ∀ x,x∉S→∀ t v,Γ (t,v) x=Γ (0,v) x)
    {ι : Type*} (μ : ι → V → ℝ) (hμ : ∀ i,ContDiff ℝ ∞ (μ i))
    (a c : ι → ℝ) (hac : ∀ i,a i < c i)
    (hY : IsCompact {v | ∀ i,μ i v ≤ c i})
    (hInv : ∀ i t x,CollarInvariant Ω (μ i) (a i) (fun v => Γ (t,v) x))
    (hnon : ∀ t∈Icc (0:ℝ) 1,∀ z∈D ×ˢ {v | ∀ i,μ i v ≤ c i},
      (globalHorizontalCoupling Ω (fun v => Γ (t,v)) z).IsInvertible) :
    ∃ e : (M × V) ≃ₘ⟮𝓘(ℝ,E × V),𝓘(ℝ,E × V)⟯ (M × V),
      e '' (D ×ˢ {v | ∀ i,μ i v ≤ c i})=D ×ˢ {v | ∀ i,μ i v ≤ c i} ∧
      e '' interior (D ×ˢ {v | ∀ i,μ i v ≤ c i})=interior (D ×ˢ {v | ∀ i,μ i v ≤ c i}) ∧
      PreservesTwoFormOn e (globalHorizontalCoupling Ω (fun v => Γ (0,v)))
        (globalHorizontalCoupling Ω (fun v => Γ (1,v))) (D ×ˢ {v | ∀ i,μ i v ≤ c i}) ∧
      (∃ C : Set (M × V),IsCompact C ∧ ∀ z,z∉C→e z=z) ∧
      (∀ z,z.1∉S→e z=z) := by
  sorry

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end
