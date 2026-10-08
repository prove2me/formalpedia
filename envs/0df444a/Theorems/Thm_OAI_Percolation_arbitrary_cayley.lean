-- Prove2me | Theorems.Thm_OAI_Percolation_arbitrary_cayley
-- name    : OAI.Percolation.arbitrary_cayley
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:01.864261+00:00
-- url     : https://prove2.me/theorems/44ffcea7-73fa-4472-b13c-bf01a37d2ad3
-- statement:
--   The theorem states that, for a finitely generated group Λ that is not amenable (in the Følner-type sense that fails: for some finite K and ε>0, no nonempty finite A has |(A·g)\A|<ε|A| for all g in K), and a finite symmetric generating set S not containing the identity, the Cayley graph whose edges are the pairs {x, xs} with s in S satisfies five conclusions for Bernoulli bond percolation, where each edge is open independently with probability p, pc is the infimum of p giving positive probability of an infinite cluster, and pu is the infimum of p for which almost surely exactly one infinite cluster exists. First, at p = pc the two-point function τ_p(x,y) = P_p(x and y are connected) is the matrix of a bounded linear operator on ℓ²(Λ), meaning there is such an operator A with (A δ_y)(x) = τ_p(x,y). Second, pc is strictly less than ptwo, the supremum of the p for which this operator-boundedness holds. Third, ptwo ≤ pu. Fourth, there exist p₁ < p₂ < 1 with pc < p₁ such that, under the coupling of independent uniform labels on edges where an edge is open at level p if its label is at most p, almost surely for every p in [p₁, p₂] the open subgraph has infinitely many infinite clusters. Fifth, for every p with pc < p < pu, almost surely the percolation configuration has infinitely many infinite clusters.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CayleyPercolation.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CayleyPercolation.lean; bytes 2341..3167
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_CayleyPercolation

namespace OAI

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

namespace Percolation

universe u v

variable {V : Type u} {E : Type v}

theorem arbitrary_cayley {Λ : Type u} [Group Λ] [Group.FG Λ]
    (hna : ¬ AmenableGroup Λ) (S : Finset Λ)
    (hsym : ∀ s ∈ S, s⁻¹ ∈ S) (hgen : Subgroup.closure (S : Set Λ) = ⊤)
    (h1 : 1 ∉ S) :
    OperatorBounded (cayleyGraph S) (pc (cayleyGraph S)) ∧
    pc (cayleyGraph S) < ptwo (cayleyGraph S) ∧
    ptwo (cayleyGraph S) ≤ pu (cayleyGraph S) ∧
    (∃ p₁ p₂ : unitInterval, pc (cayleyGraph S) < p₁ ∧ p₁ < p₂ ∧ p₂ < 1 ∧
      ∀ᵐ labels ∂(labelLaw : Measure (CayleyEdge S → unitInterval)),
        ∀ p ∈ Set.Icc p₁ p₂, (infiniteClusters (cayleyGraph S) (openEdges labels p)).Infinite) ∧
    (∀ p : unitInterval, pc (cayleyGraph S) < p → p < pu (cayleyGraph S) →
      ∀ᵐ ω ∂law p, (infiniteClusters (cayleyGraph S) ω).Infinite) := by
  sorry

end Percolation
end OAI
