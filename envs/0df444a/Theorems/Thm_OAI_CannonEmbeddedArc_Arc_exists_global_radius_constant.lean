-- Prove2me | Theorems.Thm_OAI_CannonEmbeddedArc_Arc_exists_global_radius_constant
-- name    : OAI.CannonEmbeddedArc.Arc.exists_global_radius_constant
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:47:45.505771+00:00
-- url     : https://prove2.me/theorems/9f515d10-b123-4420-bb8a-483feaef3ac1
-- title:
--   OAI.CannonEmbeddedArc.Arc.exists_global_radius_constant: intermediate lemma from OpenAI, A Modulus Proof of Cannon's Conjecture (result family 246)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CannonRelease.cannon`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Modulus Proof of Cannon's Conjecture (result family 246)*, OpenAI Math Release, September 23, 2026, result family 246, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CannonEmbeddedArc.Arc.exists_global_radius_constant` of [lean/OAI/Geometry/Cannon/Cannon/PlaneTopology/BoundaryRadiusControl.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Cannon/Cannon/PlaneTopology/BoundaryRadiusControl.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CannonEmbeddedArc.Arc`, with `open Set Metric Topology unitInterval CannonFaceIncidence CannonPackingGeometry`):
--
--   ```lean
--   theorem exists_global_radius_constant (N : ℕ) : ∃ c : ℝ,0 < c ∧ c≤1 ∧
--       ∀ {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
--         (F : ι → Arc ℂ) [Fintype (Faces F)] (out : Faces F) (B : DevelopedFaces F out),
--         Pairwise (fun i j=>Compatible (F i) (F j)) →
--         ∀ Q : Finset (ℂ × ℂ),(∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2) →
--         (∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) →
--         ∀ z : ℂ → ℂ,(∀ d,d≠out → ∀ q∈faceVertices F d,z q=B.chart d q) →
--         (∀ i,dist (z (F i 0)) (z (F i 1))=B.radius (F i 0)+B.radius (F i 1)) →
--         (∀ u,Vertex F u → ∀ v,Vertex F v → u≠v →B.radius u+B.radius v≤dist (z u) (z v)) →
--         FacialCycle F out →
--         ∀ q v j,Vertex F q → Nat.card (IncidentEdges F q)≤N →
--           Spans (F j) q v → c*B.radius q≤B.radius v
--   ```
--
--   **Definitions.** The statement is written with `OAI.CannonEmbeddedArc.Arc`, `OAI.CannonEmbeddedArc.Arc.Compatible`, `OAI.CannonEmbeddedArc.Arc.DevelopedFaces`, `OAI.CannonEmbeddedArc.Arc.Faces`, `OAI.CannonEmbeddedArc.Arc.FacialCycle`, `OAI.CannonEmbeddedArc.Arc.IncidentEdges`, `OAI.CannonEmbeddedArc.Arc.Spans`, `OAI.CannonEmbeddedArc.Arc.Vertex` and `OAI.CannonEmbeddedArc.Arc.faceVertices` (definitions bundle `OAIQ046C000` of this split).
--
--   **Used by.** The proof of `OAI.CannonRelease.boundary_packing_relative_tests` of this split imports it.
-- source:
--   OpenAI, A Modulus Proof of Cannon's Conjecture (result family 246), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 246; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Modulus-Proof-of-Cannons-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Cannon/Cannon/PlaneTopology/BoundaryRadiusControl.lean (declaration OAI.CannonEmbeddedArc.Arc.exists_global_radius_constant)

import Mathlib
import Definitions.Def_OAIQ046C000

section

attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPackingGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} [Fintype (Faces F)] {out : Faces F}
attribute [local instance] Classical.propDecidable

theorem exists_global_radius_constant (N : ℕ) : ∃ c : ℝ,0 < c ∧ c≤1 ∧
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
      (F : ι → Arc ℂ) [Fintype (Faces F)] (out : Faces F) (B : DevelopedFaces F out),
      Pairwise (fun i j=>Compatible (F i) (F j)) →
      ∀ Q : Finset (ℂ × ℂ),(∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2) →
      (∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) →
      ∀ z : ℂ → ℂ,(∀ d,d≠out → ∀ q∈faceVertices F d,z q=B.chart d q) →
      (∀ i,dist (z (F i 0)) (z (F i 1))=B.radius (F i 0)+B.radius (F i 1)) →
      (∀ u,Vertex F u → ∀ v,Vertex F v → u≠v →B.radius u+B.radius v≤dist (z u) (z v)) →
      FacialCycle F out →
      ∀ q v j,Vertex F q → Nat.card (IncidentEdges F q)≤N →
        Spans (F j) q v → c*B.radius q≤B.radius v := by
  sorry
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end
