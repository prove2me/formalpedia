-- Prove2me | Theorems.Thm_OAI_CannonEmbeddedArc_Arc_triangular_disk_gauge_integrates
-- name    : OAI.CannonEmbeddedArc.Arc.triangular_disk_gauge_integrates
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:48:13.340708+00:00
-- url     : https://prove2.me/theorems/774b9e40-0de2-4f02-b541-6312e7c36e0e
-- title:
--   OAI.CannonEmbeddedArc.Arc.triangular_disk_gauge_integrates: intermediate lemma from OpenAI, A Modulus Proof of Cannon's Conjecture (result family 246)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CannonRelease.cannon`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Modulus Proof of Cannon's Conjecture (result family 246)*, OpenAI Math Release, September 23, 2026, result family 246, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CannonEmbeddedArc.Arc.triangular_disk_gauge_integrates` of [lean/OAI/Geometry/Cannon/Cannon/PlaneTopology/NoSingleFaceDiscordance.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Cannon/Cannon/PlaneTopology/NoSingleFaceDiscordance.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CannonEmbeddedArc.Arc`, with `open Set Metric Topology unitInterval CannonFaceIncidence`):
--
--   ```lean
--   theorem triangular_disk_gauge_integrates (F : ι → Arc ℂ)
--       (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
--       (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
--       (hK : ∀ q : ℂ,IsPreconnected ((⋃i,range (F i))\{q}))
--       (out:Faces F) (hthree:(faceVertices F out).card=3)
--       (a b : ι → Faces F) (hab : ∀ i,a i≠b i)
--       (ha : ∀ i,i∈regionEdges F ConnectedComponents.mk (a i))
--       (hb : ∀ i,i∈regionEdges F ConnectedComponents.mk (b i))
--       (K : ι→D)
--       (hflat : ∀ q,Vertex F q → q∉faceVertices F out → ∃ t : Faces F→D,
--         ∀ j,q∈range (F j) → K j*t (a j)=t (b j)) :
--       ∃ v : Faces F→D,∀ i,a i≠out → b i≠out → K i*v (a i)=v (b i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CannonEmbeddedArc.Arc`, `OAI.CannonEmbeddedArc.Arc.Compatible`, `OAI.CannonEmbeddedArc.Arc.Faces`, `OAI.CannonEmbeddedArc.Arc.Vertex`, `OAI.CannonEmbeddedArc.Arc.faceVertices` and `OAI.CannonEmbeddedArc.Arc.regionEdges` (definitions bundle `OAIQ046C000` of this split).
--
--   **Used by.** The proof of `OAI.CannonEmbeddedArc.Arc.intrinsic_developed_faces` of this split imports it.
-- source:
--   OpenAI, A Modulus Proof of Cannon's Conjecture (result family 246), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 246; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Modulus-Proof-of-Cannons-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Cannon/Cannon/PlaneTopology/NoSingleFaceDiscordance.lean (declaration OAI.CannonEmbeddedArc.Arc.triangular_disk_gauge_integrates)

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
open Set Metric Topology unitInterval CannonFaceIncidence

variable {ι D : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Group D]

theorem triangular_disk_gauge_integrates (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃i,range (F i))\{q}))
    (out:Faces F) (hthree:(faceVertices F out).card=3)
    (a b : ι → Faces F) (hab : ∀ i,a i≠b i)
    (ha : ∀ i,i∈regionEdges F ConnectedComponents.mk (a i))
    (hb : ∀ i,i∈regionEdges F ConnectedComponents.mk (b i))
    (K : ι→D)
    (hflat : ∀ q,Vertex F q → q∉faceVertices F out → ∃ t : Faces F→D,
      ∀ j,q∈range (F j) → K j*t (a j)=t (b j)) :
    ∃ v : Faces F→D,∀ i,a i≠out → b i≠out → K i*v (a i)=v (b i) := by
  sorry
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end
