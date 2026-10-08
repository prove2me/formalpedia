-- Prove2me | Theorems.Thm_OAI_TriangleFace198_triangle_expansion_face
-- name    : OAI.TriangleFace198.triangle_expansion_face
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:34.597868+00:00
-- url     : https://prove2.me/theorems/1a9898b7-f905-4369-bf19-93924145ef63
-- statement:
--   The theorem states that for a finite loopless multigraph G (each edge e has distinct endpoints left e and right e) and a vertex v incident to exactly three edges, and assuming G has at least one perfect matching (a hypothesis not otherwise used), there is a labelling c of the edges by Fin 3 = {0,1,2} such that each label is carried by exactly one edge incident to v, with the following properties. Let H be the triangle expansion of G at v: v is replaced by a triangle on three new vertices (v itself and two extra vertices), each old edge keeps its other endpoint but any endpoint equal to v is moved to the triangle vertex with the edge's label, and three new edges i in Fin 3 are added, edge i joining triangle vertices i+1 and i+2. Let f be the linear map from edge-weight vectors of G to those of H that keeps the weight on each old edge and gives new edge i the weight of the unique edge at v labelled i. Let Q be the set of points of the matching polytope of H (the convex hull of perfect-matching indicator vectors) whose total weight on edges crossing the cut around the three triangle vertices equals 1. Then f maps the matching polytope of G exactly onto Q; Q is convex and is an extreme subset (a face) of H's polytope; restricting f(x) to the old edges recovers x; f(oldRestriction y)=y for every y in Q; f(x) agrees with x on old edges and with the labelled local edges on new edges; f sends the all-1/3 vector to the all-1/3 vector; and for every x in G's polytope, the minimal face of H's polytope containing f(x) is the image under f of the minimal face of G's polytope containing x, where the minimal face is the intersection of all convex extreme subsets containing the point.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/TriangleFace.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/TriangleFace.lean; bytes 5338..6289
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_TriangleFace

namespace OAI

noncomputable section

open scoped BigOperators

open MatchingEntropyBounds MatchingEntropyBounds.Refined

namespace TriangleFace198

universe uV uE

variable {V : Type uV} {E : Type uE} [instFintypeV : Fintype V] [Fintype E] [DecidableEq V] [instDecidableEqE : DecidableEq E]

theorem triangle_expansion_face {V : Type uV} {E : Type uE}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : LooplessGraph V E) (v : V)
    (hdeg : Fintype.card {e : E // G.Incident v e} = 3)
    (_hmatching : Nonempty G.Matching) :
    ∃ (c : E → Fin 3) (hc : LocalLabels G v c),
      let H := triangleExpansion G c v
      let f := localExtension G c v hc
      let Q := {y | y ∈ H.polytope ∧ H.cutMass y (triangleVertices v) = 1}
      f '' G.polytope = Q ∧
      Convex ℝ Q ∧ IsExtreme ℝ H.polytope Q ∧
      (∀ x, oldRestriction (f x) = x) ∧
      (∀ y ∈ Q, f (oldRestriction y) = y) ∧
      (∀ x e, f x (Sum.inl e) = x e) ∧
      (∀ x i, f x (Sum.inr i) = x (localEdge G c v hc i)) ∧
      (∀ x, (∀ e, x e = (1/3 : ℝ)) → ∀ e, f x e = (1/3 : ℝ)) ∧
      (∀ x ∈ G.polytope, CanonicalFace198.minFace H.polytope (f x) = f '' CanonicalFace198.minFace G.polytope x)  := by
  sorry

end TriangleFace198
end
end OAI
