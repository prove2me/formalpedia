-- Prove2me | Theorems.Thm_OAI_CannonEmbeddedArc_Arc_DevelopedFaces_hull_geometry
-- name    : OAI.CannonEmbeddedArc.Arc.DevelopedFaces.hull_geometry
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:47:09.489449+00:00
-- url     : https://prove2.me/theorems/64366169-75cf-4d03-b21c-f36dd6375b11
-- title:
--   OAI.CannonEmbeddedArc.Arc.DevelopedFaces.hull_geometry: intermediate lemma from OpenAI, A Modulus Proof of Cannon's Conjecture (result family 246)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CannonRelease.cannon`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Modulus Proof of Cannon's Conjecture (result family 246)*, OpenAI Math Release, September 23, 2026, result family 246, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CannonEmbeddedArc.Arc.DevelopedFaces.hull_geometry` of [lean/OAI/Geometry/Cannon/Cannon/PlaneTopology/ClosedInsideSegment.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Cannon/Cannon/PlaneTopology/ClosedInsideSegment.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CannonEmbeddedArc.Arc`, with `open Set Metric Topology CannonFaceIncidence CannonTriangleWinding`):
--
--   ```lean
--   theorem DevelopedFaces.hull_geometry (B : DevelopedFaces F out)
--       (hF : Pairwise fun i j=>Compatible (F i) (F j))
--       (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
--       (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
--       (hthree : ∀ d,(faceVertices F d).card=3)
--       (z : ℂ → ℂ) (hz : ∀ d,d≠out → ∀ q∈faceVertices F d,z q=B.chart d q) :
--       (∀ d : Faces F,∃ C : FacialCycle F d,0<area (z C.a) (z C.b) (z C.c)) ∧
--       (∀ d e : Faces F,d≠out → e≠out → d≠e →
--         Disjoint (interior (faceHull F z d)) (interior (faceHull F z e))) ∧
--       (⋃ d : {d : Faces F // d≠out},faceHull F z d.val)=faceHull F z out
--   ```
--
--   **Definitions.** The statement is written with `OAI.CannonEmbeddedArc.Arc`, `OAI.CannonEmbeddedArc.Arc.Compatible`, `OAI.CannonEmbeddedArc.Arc.DevelopedFaces`, `OAI.CannonEmbeddedArc.Arc.Faces`, `OAI.CannonEmbeddedArc.Arc.FacialCycle`, `OAI.CannonEmbeddedArc.Arc.faceHull` and `OAI.CannonEmbeddedArc.Arc.faceVertices` (definitions bundle `OAIQ046C000` of this split); `OAI.CannonTriangleWinding.area` (definitions bundle `OAIQ046C001` of this split).
--
--   **Used by.** The proof of `OAI.CannonRelease.boundary_packing_relative_tests` of this split imports it.
-- source:
--   OpenAI, A Modulus Proof of Cannon's Conjecture (result family 246), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 246; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Modulus-Proof-of-Cannons-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Cannon/Cannon/PlaneTopology/ClosedInsideSegment.lean (declaration OAI.CannonEmbeddedArc.Arc.DevelopedFaces.hull_geometry)

import Mathlib
import Definitions.Def_OAIQ046C000
import Definitions.Def_OAIQ046C001

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
open Set Metric Topology CannonFaceIncidence CannonTriangleWinding

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} [Fintype (Faces F)] {out : Faces F}

theorem DevelopedFaces.hull_geometry (B : DevelopedFaces F out)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (hthree : ∀ d,(faceVertices F d).card=3)
    (z : ℂ → ℂ) (hz : ∀ d,d≠out → ∀ q∈faceVertices F d,z q=B.chart d q) :
    (∀ d : Faces F,∃ C : FacialCycle F d,0<area (z C.a) (z C.b) (z C.c)) ∧
    (∀ d e : Faces F,d≠out → e≠out → d≠e →
      Disjoint (interior (faceHull F z d)) (interior (faceHull F z e))) ∧
    (⋃ d : {d : Faces F // d≠out},faceHull F z d.val)=faceHull F z out := by
  sorry
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end
