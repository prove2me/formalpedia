-- Prove2me | Theorems.Thm_OAI_Percolation_BenjaminiSchramm_critical_laws
-- name    : OAI.Percolation.BenjaminiSchramm.critical_laws
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:01.563738+00:00
-- url     : https://prove2.me/theorems/4d624472-a84e-4138-8445-745c907e1fa0
-- statement:
--   The theorem states that for a bond graph G (a vertex type V with an edge type E and a map sending each edge to an unordered pair of endpoints) on an infinite vertex set, if G is connected, locally finite (each vertex lies in finitely many edges), quasi-transitive (finitely many vertex representatives such that every vertex is the image of one of them under an automorphism of G), and has positive vertex-isoperimetric constant hV(G) > 0 (the infimum over nonempty finite sets A of the number of outside vertices adjacent to A divided by |A|), then a bundle of critical-percolation conclusions holds for Bernoulli bond percolation with critical parameter pc(G). First, for every vertex x, the triangle diagram at pc, the sum over pairs (a,b) of the product of two-point connection probabilities τ(x,a)τ(a,b)τ(b,x), is finite and at most the cube of the operator norm of the two-point kernel at pc. Second, the susceptibility (the sum over y of τ(x,y)) satisfies c/(pc−p) ≤ χ_p(x) ≤ C/(pc−p) for p slightly below pc, with positive constants depending on x. Third, the probability that x lies in an infinite cluster lies between c(p−pc) and C(p−pc) for p slightly above pc. Fourth, at pc, the probabilities that the cluster of x has at least n vertices, reaches intrinsic (open-graph) distance at least n, or reaches graph distance at least n, decay like n^(−1/2), n^(−1) and n^(−1) respectively, bounded above and below by positive constant multiples for all n ≥ 1. Fifth, pc < ptwo ≤ pexp, where ptwo is the supremum of parameters at which the two-point function defines a bounded operator on ℓ² and pexp is the supremum of parameters with exponential decay of connection probabilities in graph distance. Finally, for every p < ptwo, the two-point function satisfies τ_p(x,y) ≤ A·exp(−a·d(x,y)) for some positive constants A and a that are uniform in x and y. The theorem is admitted in the source, not proved there.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BenjaminiSchramm.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BenjaminiSchramm.lean; bytes 8256..8567
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_BenjaminiSchramm

namespace OAI

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

namespace Percolation.BenjaminiSchramm

universe u v

/-- Critical mean-field laws and uniform exponential connectivity below the operator threshold. -/
theorem critical_laws {V : Type u} {E : Type v} [Infinite V]
    (G : BondGraph V E) (hc : Connected G) (hl : LocallyFinite G)
    (hq : QuasiTransitive G) (hh : 0 < hV G) : CriticalLawsConclusion G := by
  sorry

end Percolation.BenjaminiSchramm
end OAI
