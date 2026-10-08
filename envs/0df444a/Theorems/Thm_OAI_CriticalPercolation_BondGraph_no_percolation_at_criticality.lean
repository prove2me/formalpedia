-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_no_percolation_at_criticality
-- name    : OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:30.212237+00:00
-- url     : https://prove2.me/theorems/d199ca2a-548e-4919-ae6c-f11775c12b5c
-- statement:
--   The theorem states that, for a bond graph G with vertex type V and bond-label type E (an undirected graph in which each bond has an unordered pair of endpoints, so loops and parallel bonds are allowed), if V is infinite, the full graph with every bond retained is connected (loops being discarded in this simple-graph connectivity), G is locally finite in the sense that each vertex is an endpoint of only finitely many bonds counted with multiplicity, and G is quasi-transitive, meaning there is a finite set of vertices such that every vertex is the image of one of them under an automorphism of G (a pair of bijections of vertices and bonds preserving endpoint structure), and if the critical probability is strictly less than 1, then Bernoulli bond percolation at exactly the critical probability has probability zero of percolating. Here each bond is independently retained with probability p, an open cluster of v is the set of vertices reachable from v by finite paths of retained bonds, percolation is the event that some open cluster is infinite, and the critical probability is the infimum of those p in [0,1] for which percolation has positive probability.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CriticalPercolation.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CriticalPercolation.lean; bytes 1835..2204
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_CriticalPercolation

namespace OAI

open Set MeasureTheory ProbabilityTheory

namespace CriticalPercolation

namespace BondGraph

variable {V E : Type*} (G : BondGraph V E)

/-- Critical Bernoulli bond percolation has no infinite cluster when the critical
probability is below one. -/
theorem no_percolation_at_criticality [Infinite V]
    (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite)
    (hquasi : G.QuasiTransitive)
    (hpc : G.criticalProbability < 1) :
    G.law G.criticalProbability G.percolates = 0 := by
  sorry

end BondGraph
end CriticalPercolation
end OAI
