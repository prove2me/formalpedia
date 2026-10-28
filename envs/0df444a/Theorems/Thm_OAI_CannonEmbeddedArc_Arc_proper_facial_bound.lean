-- Prove2me | Theorems.Thm_OAI_CannonEmbeddedArc_Arc_proper_facial_bound
-- name    : OAI.CannonEmbeddedArc.Arc.proper_facial_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:49:33.873132+00:00
-- url     : https://prove2.me/theorems/4205a864-19cf-42ea-89b3-7765135d6a96
-- title:
--   OAI.CannonEmbeddedArc.Arc.proper_facial_bound: intermediate lemma from OpenAI, A Modulus Proof of Cannon's Conjecture (result family 246)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CannonRelease.cannon`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Modulus Proof of Cannon's Conjecture (result family 246)*, OpenAI Math Release, September 23, 2026, result family 246, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CannonEmbeddedArc.Arc.proper_facial_bound` of [lean/OAI/Geometry/Cannon/Cannon/PlaneTopology/MetricStarFlat.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Cannon/Cannon/PlaneTopology/MetricStarFlat.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CannonEmbeddedArc.Arc`, with `open Set Topology unitInterval CannonFaceIncidence CannonPlanarEuler`):
--
--   ```lean
--   theorem proper_facial_bound (F : ι → Arc ℂ)
--       (hF : Pairwise (fun i j => Compatible (F i) (F j)))
--       (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2)
--       (hthree : ∀ d : Faces F,3≤Nat.card (regionEdges F ConnectedComponents.mk d))
--       (T : Finset ℂ) (hproper : ¬vertices F Finset.univ⊆T)
--       (hB : ∃ d : Faces F,faceVertices F d⊆T) :
--       Nat.card {d : Faces F | faceVertices F d⊆T}+5≤2*T.card
--   ```
--
--   **Definitions.** The statement is written with `OAI.CannonEmbeddedArc.Arc`, `OAI.CannonPlanarEuler.vertices`, `OAI.CannonEmbeddedArc.Arc.Compatible`, `OAI.CannonEmbeddedArc.Arc.Faces`, `OAI.CannonEmbeddedArc.Arc.faceVertices` and `OAI.CannonEmbeddedArc.Arc.regionEdges` (definitions bundle `OAIQ046C000` of this split).
--
--   **Used by.** The proof of `OAI.CannonRelease.boundary_uniform_circle_packing` of this split imports it.
-- source:
--   OpenAI, A Modulus Proof of Cannon's Conjecture (result family 246), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 246; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Modulus-Proof-of-Cannons-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Cannon/Cannon/PlaneTopology/MetricStarFlat.lean (declaration OAI.CannonEmbeddedArc.Arc.proper_facial_bound)

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
open Set Topology unitInterval CannonFaceIncidence CannonPlanarEuler

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem proper_facial_bound (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2)
    (hthree : ∀ d : Faces F,3≤Nat.card (regionEdges F ConnectedComponents.mk d))
    (T : Finset ℂ) (hproper : ¬vertices F Finset.univ⊆T)
    (hB : ∃ d : Faces F,faceVertices F d⊆T) :
    Nat.card {d : Faces F | faceVertices F d⊆T}+5≤2*T.card := by
  sorry
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end
