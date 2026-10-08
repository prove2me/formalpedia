-- Prove2me | Theorems.Thm_OAI_Percolation_BenjaminiSchramm_full_main
-- name    : OAI.Percolation.BenjaminiSchramm.full_main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:01.70999+00:00
-- url     : https://prove2.me/theorems/e98a63da-1ea3-40f0-ba06-723609f6a524
-- statement:
--   The theorem states that for a bond graph G, given by a map from an edge type E to unordered pairs of vertices in an infinite vertex type V, that is connected, locally finite (each vertex lies in finitely many edges) and quasi-transitive (finitely many vertex representatives such that every vertex is the image of one under an automorphism of G acting on vertices and edges), and whose vertex isoperimetric constant hV(G), the infimum over nonempty finite vertex sets A of |outer vertex boundary of A|/|A|, is strictly positive, the MainConclusion holds for Bernoulli bond percolation on G. Writing pc for the infimum of parameters p at which an infinite cluster occurs with positive probability, pu for the infimum of p at which there is almost surely exactly one infinite cluster, ptwo for the supremum of p at which the two-point function τ_p(x,y)=P_p(x connected to y) is the matrix kernel of a bounded operator on ℓ²(V), and operatorNorm(p) for the infimum of operator norms of such operators, valued in [0,∞], the conclusion has four parts. First, the supremum of operatorNorm(p) over p<pc equals operatorNorm(pc). Second, operatorNorm(pc) is finite. Third, pc<ptwo≤pu. Fourth, there exist p₁<p₂<1 with pc<p₁ such that, for almost every i.i.d. uniform [0,1] edge labelling, for every p in [p₁,p₂] the configuration of edges with label at most p has infinitely many infinite clusters. The proof is omitted (sorry) in the source.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BenjaminiSchramm.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BenjaminiSchramm.lean; bytes 7965..8254
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_BenjaminiSchramm

namespace OAI

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

namespace Percolation.BenjaminiSchramm

universe u v

/-- Critical operator boundedness, the threshold gap, and simultaneous nonuniqueness. -/
theorem full_main {V : Type u} {E : Type v} [Infinite V]
    (G : BondGraph V E) (hc : Connected G) (hl : LocallyFinite G)
    (hq : QuasiTransitive G) (hh : 0 < hV G) : MainConclusion G := by
  sorry

end Percolation.BenjaminiSchramm
end OAI
