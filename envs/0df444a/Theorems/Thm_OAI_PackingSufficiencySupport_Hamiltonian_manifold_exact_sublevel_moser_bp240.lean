-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_manifold_exact_sublevel_moser_bp240
-- name    : OAI.PackingSufficiencySupport.Hamiltonian.manifold_exact_sublevel_moser_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:48:27.560194+00:00
-- url     : https://prove2.me/theorems/42e2857a-0aed-43c9-b290-8d84db5487f8
-- title:
--   OAI.PackingSufficiencySupport.Hamiltonian.manifold_exact_sublevel_moser_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.Hamiltonian.manifold_exact_sublevel_moser` of [lean/OAI/Geometry/BallPacking/Flows/NonautonomousManifoldFlow.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Flows/NonautonomousManifoldFlow.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.Hamiltonian`, with `open scoped ContDiff Manifold Topology`, `open Set Function Manifold`):
--
--   ```lean
--   theorem manifold_exact_sublevel_moser_bp240
--       {Γ : ℝ → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
--       {ι : Type*} (μ : ι → M → ℝ)
--       (hμ : ∀ i, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (μ i))
--       (a c : ι → ℝ) (hac : ∀ i, a i < c i)
--       (hD : IsCompact {x | ∀ i, μ i x ≤ c i})
--       {U : Set (ℝ × M)} (hU : IsOpen U)
--       (hDU : Icc (0:ℝ) 1 ×ˢ {x | ∀ i, μ i x ≤ c i} ⊆ U)
--       (hinv : ∀ p ∈ U, (manifoldExteriorOneForm (Γ p.1) p.2).IsInvertible)
--       (Z : ι → M → E)
--       (hface : ∀ i p, p ∈ U → a i<μ i p.2 →
--         (∀ t, Γ t p.2=Γ 0 p.2) ∨
--         (manifoldExteriorOneForm (Γ p.1) p.2 (Z i p.2) = -mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (μ i) p.2 ∧
--           ∀ t, Γ t p.2 (Z i p.2)=Γ 0 p.2 (Z i p.2))) :
--       ∃ Φ Ψ : ℝ × M → M,
--         ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Φ ∧
--         ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Ψ ∧
--         (∀ x, Φ (0,x)=x) ∧
--         (∀ t ∈ Icc (0:ℝ) 1, ∀ x, Ψ (t,Φ (t,x))=x ∧ Φ (t,Ψ (t,x))=x) ∧
--         (∃ C : Set M, IsCompact C ∧ ∀ t x, x ∉ C → Φ (t,x)=x) ∧
--         (∀ x, (∀ t, Γ t x=Γ 0 x) → ∀ t, Φ (t,x)=x) ∧
--         (∀ t ∈ Icc (0:ℝ) 1,
--           (fun x => Φ (t,x)) '' {x | ∀ i, μ i x ≤ c i}={x | ∀ i, μ i x ≤ c i} ∧
--           (fun x => Φ (t,x)) '' interior {x | ∀ i, μ i x ≤ c i}=interior {x | ∀ i, μ i x ≤ c i}) ∧
--         (∀ t ∈ Icc (0:ℝ) 1, ∀ x, (∀ i, μ i x ≤ c i) → ∀ v w,
--           manifoldPullback Φ (fun s => manifoldExteriorOneForm (Γ s)) t x v w=
--             manifoldExteriorOneForm (Γ 0) x v w)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.SmoothOneFormFamily` and `OAI.PackingSufficiencySupport.Hamiltonian.manifoldExteriorOneForm` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.manifoldPullback` (definitions bundle `OAIQ240Bp007` of this split).
--
--   **Used by.** The proof of `OAI.PackingSufficiencySupport.Hamiltonian.horizontal_moser_endpoint_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Flows/NonautonomousManifoldFlow.lean (declaration OAI.PackingSufficiencySupport.Hamiltonian.manifold_exact_sublevel_moser)

import Mathlib
import Definitions.Def_OAIQ240Bp007

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
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem manifold_exact_sublevel_moser_bp240
    {Γ : ℝ → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
    {ι : Type*} (μ : ι → M → ℝ)
    (hμ : ∀ i, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (μ i))
    (a c : ι → ℝ) (hac : ∀ i, a i < c i)
    (hD : IsCompact {x | ∀ i, μ i x ≤ c i})
    {U : Set (ℝ × M)} (hU : IsOpen U)
    (hDU : Icc (0:ℝ) 1 ×ˢ {x | ∀ i, μ i x ≤ c i} ⊆ U)
    (hinv : ∀ p ∈ U, (manifoldExteriorOneForm (Γ p.1) p.2).IsInvertible)
    (Z : ι → M → E)
    (hface : ∀ i p, p ∈ U → a i<μ i p.2 →
      (∀ t, Γ t p.2=Γ 0 p.2) ∨
      (manifoldExteriorOneForm (Γ p.1) p.2 (Z i p.2) = -mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (μ i) p.2 ∧
        ∀ t, Γ t p.2 (Z i p.2)=Γ 0 p.2 (Z i p.2))) :
    ∃ Φ Ψ : ℝ × M → M,
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Φ ∧
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Ψ ∧
      (∀ x, Φ (0,x)=x) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ x, Ψ (t,Φ (t,x))=x ∧ Φ (t,Ψ (t,x))=x) ∧
      (∃ C : Set M, IsCompact C ∧ ∀ t x, x ∉ C → Φ (t,x)=x) ∧
      (∀ x, (∀ t, Γ t x=Γ 0 x) → ∀ t, Φ (t,x)=x) ∧
      (∀ t ∈ Icc (0:ℝ) 1,
        (fun x => Φ (t,x)) '' {x | ∀ i, μ i x ≤ c i}={x | ∀ i, μ i x ≤ c i} ∧
        (fun x => Φ (t,x)) '' interior {x | ∀ i, μ i x ≤ c i}=interior {x | ∀ i, μ i x ≤ c i}) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ x, (∀ i, μ i x ≤ c i) → ∀ v w,
        manifoldPullback Φ (fun s => manifoldExteriorOneForm (Γ s)) t x v w=
          manifoldExteriorOneForm (Γ 0) x v w) := by
  sorry

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end
