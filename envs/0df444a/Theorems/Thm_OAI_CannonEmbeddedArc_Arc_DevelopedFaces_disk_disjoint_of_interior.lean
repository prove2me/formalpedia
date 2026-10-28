-- Prove2me | Theorems.Thm_OAI_CannonEmbeddedArc_Arc_DevelopedFaces_disk_disjoint_of_interior
-- name    : OAI.CannonEmbeddedArc.Arc.DevelopedFaces.disk_disjoint_of_interior
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:46:44.648458+00:00
-- url     : https://prove2.me/theorems/b13d97c5-6abd-4e33-af7b-c7c1d2e6ef2c
-- title:
--   OAI.CannonEmbeddedArc.Arc.DevelopedFaces.disk_disjoint_of_interior: intermediate lemma from OpenAI, A Modulus Proof of Cannon's Conjecture (result family 246)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CannonRelease.cannon`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Modulus Proof of Cannon's Conjecture (result family 246)*, OpenAI Math Release, September 23, 2026, result family 246, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CannonEmbeddedArc.Arc.DevelopedFaces.disk_disjoint_of_interior` of [lean/OAI/Geometry/Cannon/Cannon/PlaneTopology/BoundaryBallCover.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Cannon/Cannon/PlaneTopology/BoundaryBallCover.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CannonEmbeddedArc.Arc`, with `open Set Metric Topology unitInterval CannonFaceIncidence CannonPackingGeometry CannonTriangleBoundary`):
--
--   ```lean
--   theorem DevelopedFaces.disk_disjoint_of_interior (B : DevelopedFaces F out)
--       (hF : Pairwise fun i j=>Compatible (F i) (F j))
--       (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
--       (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
--       (z : ℂ → ℂ) (hz : ∀ d,d≠out → ∀ q∈faceVertices F d,z q=B.chart d q)
--       (hlen : ∀ i,dist (z (F i 0)) (z (F i 1))=B.radius (F i 0)+B.radius (F i 1))
--       (C : ∀ d : {d : Faces F // d≠out},FacialCycle F d.val) (O : FacialCycle F out)
--       (hpos : ∀ d,0<CannonTriangleWinding.area (z (C d).a) (z (C d).b) (z (C d).c))
--       (ho : 0<CannonTriangleWinding.area (z O.a) (z O.b) (z O.c))
--       (hchain : ∀ f : ℂ → ℂ → ℤ,(∀ x y,f y x= -f x y) →
--         (∑ d,cycle (fun x y=>f (z x) (z y)) (C d).a (C d).b (C d).c)=
--           cycle f (z O.a) (z O.b) (z O.c))
--       (hdis : Pairwise (fun d e=>Disjoint
--         {p | CannonTriangleWinding.Inside (z (C d).a) (z (C d).b) (z (C d).c) p}
--         {p | CannonTriangleWinding.Inside (z (C e).a) (z (C e).b) (z (C e).c) p}))
--       {q v : ℂ} (hq : Vertex F q) (hv : Vertex F v)
--       (hqo : q∉faceVertices F out) (hqv : q≠v) :
--       Disjoint (ball (z q) (B.radius q)) (ball (z v) (B.radius v))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CannonEmbeddedArc.Arc`, `OAI.CannonEmbeddedArc.Arc.Compatible`, `OAI.CannonEmbeddedArc.Arc.DevelopedFaces`, `OAI.CannonEmbeddedArc.Arc.Faces`, `OAI.CannonEmbeddedArc.Arc.FacialCycle`, `OAI.CannonEmbeddedArc.Arc.Vertex` and `OAI.CannonEmbeddedArc.Arc.faceVertices` (definitions bundle `OAIQ046C000` of this split); `OAI.CannonTriangleBoundary.cycle`, `OAI.CannonTriangleWinding.Inside` and `OAI.CannonTriangleWinding.area` (definitions bundle `OAIQ046C001` of this split).
--
--   **Used by.** The proofs of `OAI.CannonEmbeddedArc.Arc.DevelopedFaces.circle_packing` and `OAI.CannonRelease.boundary_packing_relative_tests` of this split import it.
-- source:
--   OpenAI, A Modulus Proof of Cannon's Conjecture (result family 246), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 246; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Modulus-Proof-of-Cannons-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Cannon/Cannon/PlaneTopology/BoundaryBallCover.lean (declaration OAI.CannonEmbeddedArc.Arc.DevelopedFaces.disk_disjoint_of_interior)

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
open Set Metric Topology unitInterval CannonFaceIncidence CannonPackingGeometry CannonTriangleBoundary

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} [Fintype (Faces F)] {out : Faces F}
attribute [local instance] Classical.propDecidable

theorem DevelopedFaces.disk_disjoint_of_interior (B : DevelopedFaces F out)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (z : ℂ → ℂ) (hz : ∀ d,d≠out → ∀ q∈faceVertices F d,z q=B.chart d q)
    (hlen : ∀ i,dist (z (F i 0)) (z (F i 1))=B.radius (F i 0)+B.radius (F i 1))
    (C : ∀ d : {d : Faces F // d≠out},FacialCycle F d.val) (O : FacialCycle F out)
    (hpos : ∀ d,0<CannonTriangleWinding.area (z (C d).a) (z (C d).b) (z (C d).c))
    (ho : 0<CannonTriangleWinding.area (z O.a) (z O.b) (z O.c))
    (hchain : ∀ f : ℂ → ℂ → ℤ,(∀ x y,f y x= -f x y) →
      (∑ d,cycle (fun x y=>f (z x) (z y)) (C d).a (C d).b (C d).c)=
        cycle f (z O.a) (z O.b) (z O.c))
    (hdis : Pairwise (fun d e=>Disjoint
      {p | CannonTriangleWinding.Inside (z (C d).a) (z (C d).b) (z (C d).c) p}
      {p | CannonTriangleWinding.Inside (z (C e).a) (z (C e).b) (z (C e).c) p}))
    {q v : ℂ} (hq : Vertex F q) (hv : Vertex F v)
    (hqo : q∉faceVertices F out) (hqv : q≠v) :
    Disjoint (ball (z q) (B.radius q)) (ball (z v) (B.radius v)) := by
  sorry

end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end
