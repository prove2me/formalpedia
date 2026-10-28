-- Prove2me | Theorems.Thm_OAI_CannonRelease_boundary_uniform_controlled_faces
-- name    : OAI.CannonRelease.boundary_uniform_controlled_faces
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:52:28.073244+00:00
-- url     : https://prove2.me/theorems/e8cdd448-0da5-465d-8409-1e5a5570c7ef
-- title:
--   OAI.CannonRelease.boundary_uniform_controlled_faces: intermediate lemma from OpenAI, A Modulus Proof of Cannon's Conjecture (result family 246)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CannonRelease.cannon`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Modulus Proof of Cannon's Conjecture (result family 246)*, OpenAI Math Release, September 23, 2026, result family 246, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CannonRelease.boundary_uniform_controlled_faces` of [lean/OAI/Geometry/Cannon/Cannon/PlanarGraphs/TraceCard.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Cannon/Cannon/PlanarGraphs/TraceCard.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CannonRelease`, with `open Set unitInterval Topology`, `open Set Topology unitInterval`, `open Set Metric Topology unitInterval`, `open Set Metric Topology`, `open Set unitInterval`, `open Set Metric Topology`, `open Set Metric Topology`, `open Set Metric Topology`, `open Set Topology`, `open Set Topology`, `open Set Topology`, `open Set Metric Topology unitInterval CannonGraph CannonRegularDisk CannonEmbeddedArc CannonEmbeddedArc.Arc`):
--
--   ```lean
--   theorem boundary_uniform_controlled_faces (φ : Boundary D ≃ₜ SphereTwo) :
--       let _ := visualMetricSpace D hδ
--       ∃ A L r₀ : ℝ, 1≤A ∧ 1≤L ∧ 0 < r₀ ∧ ∃ K J : ℕ,
--         ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ T : Finset (Boundary D),
--         (∀ x∈T, ∀ y∈T, x≠y → r≤dist x y) →
--         (∀ x : Boundary D, ∃ y∈T, dist x y ≤ r) →
--         ∀ p : Boundary D, p∉T →
--         ∃ e : ℂ → Boundary D, IsOpenEmbedding e ∧ range e={p}ᶜ ∧
--         ∃ Q : Finset (ℂ × ℂ), ∃ n : ℕ, 0<n ∧ ∃ F : Fin n → Arc (Boundary D),
--           Pairwise (fun i j => Compatible (F i) (F j)) ∧
--           (∀ j, diam (range (F j))≤A*r) ∧
--           (∀ x, intersectionCount F (ball x (2*A*r))≤K) ∧
--           (∀ x, intersectionCount F (ball x ((L+1)*r))≤J) ∧
--           IsPathConnected (⋃ j,range (F j)) ∧ (T:Set (Boundary D))⊆(⋃ j,range (F j)) ∧
--           (⋃ j,range (F j))⊆e '' (⋃ q∈Q,segment ℝ q.1 q.2) ∧
--           Finite (ConnectedComponents ((⋃ j,range (F j))ᶜ : Set (Boundary D))) ∧
--           (∀ R : Set (Boundary D), IsPreconnected R → R⊆(⋃ j,range (F j))ᶜ →
--             ∀ x∈R, ∀ y∈R, dist x y<L*r) ∧
--           (let Faces := ConnectedComponents ((⋃ j,range (F j))ᶜ : Set (Boundary D))
--            let π : ((⋃ j,range (F j))ᶜ : Set (Boundary D)) → Faces := ConnectedComponents.mk
--            ∃ (S : Faces → Set (Fin n)) (labels : Fin n → Bool → Faces),
--              (∀ d, closure (region _ π d)=region _ π d∪⋃ i∈S d,range (F i)) ∧
--              (∀ d i, i∈S d ↔ d∈range (labels i)) ∧
--              (∀ d, Nat.card (S d)≤J))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CannonEmbeddedArc.Arc`, `OAI.CannonFaceIncidence.region`, `OAI.CannonGraph.Thin`, `OAI.CannonEmbeddedArc.Arc.Compatible` and `OAI.CannonEmbeddedArc.Arc.intersectionCount` (definitions bundle `OAIQ046C000` of this split); `OAI.CannonRelease.visualMetricSpace` (definitions bundle `OAIQ046C002` of this split); `OAI.CannonRelease.Boundary`, `OAI.CannonRelease.CayleyData`, `OAI.CannonRelease.SphereTwo`, `OAI.CannonRelease.instTopologicalSpaceBoundary` and `OAI.CannonRelease.CayleyData.graph` (the published bundle `Def_CannonGeometricAction`).
--
--   **Used by.** The proof of `OAI.CannonRelease.boundary_uniform_circle_packing` of this split imports it.
-- source:
--   OpenAI, A Modulus Proof of Cannon's Conjecture (result family 246), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 246; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Modulus-Proof-of-Cannons-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Cannon/Cannon/PlanarGraphs/TraceCard.lean (declaration OAI.CannonRelease.boundary_uniform_controlled_faces)

import Mathlib
import Definitions.Def_CannonGeometricAction
import Definitions.Def_OAIQ046C002

section

attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

namespace CannonRelease
open Set Metric Topology unitInterval CannonGraph CannonRegularDisk CannonEmbeddedArc CannonEmbeddedArc.Arc

  CannonFaceIncidence CannonPlaneLinear CannonIncidence
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_uniform_controlled_faces (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ A L r₀ : ℝ, 1≤A ∧ 1≤L ∧ 0 < r₀ ∧ ∃ K J : ℕ,
      ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ T : Finset (Boundary D),
      (∀ x∈T, ∀ y∈T, x≠y → r≤dist x y) →
      (∀ x : Boundary D, ∃ y∈T, dist x y ≤ r) →
      ∀ p : Boundary D, p∉T →
      ∃ e : ℂ → Boundary D, IsOpenEmbedding e ∧ range e={p}ᶜ ∧
      ∃ Q : Finset (ℂ × ℂ), ∃ n : ℕ, 0<n ∧ ∃ F : Fin n → Arc (Boundary D),
        Pairwise (fun i j => Compatible (F i) (F j)) ∧
        (∀ j, diam (range (F j))≤A*r) ∧
        (∀ x, intersectionCount F (ball x (2*A*r))≤K) ∧
        (∀ x, intersectionCount F (ball x ((L+1)*r))≤J) ∧
        IsPathConnected (⋃ j,range (F j)) ∧ (T:Set (Boundary D))⊆(⋃ j,range (F j)) ∧
        (⋃ j,range (F j))⊆e '' (⋃ q∈Q,segment ℝ q.1 q.2) ∧
        Finite (ConnectedComponents ((⋃ j,range (F j))ᶜ : Set (Boundary D))) ∧
        (∀ R : Set (Boundary D), IsPreconnected R → R⊆(⋃ j,range (F j))ᶜ →
          ∀ x∈R, ∀ y∈R, dist x y<L*r) ∧
        (let Faces := ConnectedComponents ((⋃ j,range (F j))ᶜ : Set (Boundary D))
         let π : ((⋃ j,range (F j))ᶜ : Set (Boundary D)) → Faces := ConnectedComponents.mk
         ∃ (S : Faces → Set (Fin n)) (labels : Fin n → Bool → Faces),
           (∀ d, closure (region _ π d)=region _ π d∪⋃ i∈S d,range (F i)) ∧
           (∀ d i, i∈S d ↔ d∈range (labels i)) ∧
           (∀ d, Nat.card (S d)≤J)) := by
  sorry
end CannonRelease

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end
