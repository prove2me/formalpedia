-- Prove2me | Theorems.Thm_OAI_Percolation_BenjaminiSchramm_cayley_main
-- name    : OAI.Percolation.BenjaminiSchramm.cayley_main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:01.409379+00:00
-- url     : https://prove2.me/theorems/d71a279a-01f1-4007-bce6-3586e0f4fcce
-- statement:
--   The theorem states that, for a group Λ with a finite generating set S that is closed under inverses, does not contain the identity, and generates Λ as a group, if Λ is not Følner-amenable, then the bond-percolation model on its Cayley graph (vertices are group elements, edges join x and x·s for s in S) satisfies three conclusions. Here Følner-amenable means that for every finite K and every ε>0 there is a nonempty finite A with |(A·k) \ A| < ε|A| for all k in K. First, the two-point function of Bernoulli bond percolation at the critical parameter pc, namely the probability that x and y are joined by an open path, is the matrix of a bounded operator on ℓ²(Λ). Second, the MainConclusion property holds: the supremum of the operator norms of the two-point kernel over p<pc equals its norm at pc, this norm is finite, pc < ptwo ≤ pu, where ptwo is the supremum of parameters at which the kernel is a bounded operator and pu is the uniqueness threshold, and there exist p₁<p₂<1 with pc<p₁ such that, almost surely for independent uniform edge labels, for every p in [p₁,p₂] the subgraph of edges with label at most p has infinitely many infinite clusters. Third, for every p with pc < p < pu, Bernoulli(p) percolation almost surely has infinitely many infinite clusters.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BenjaminiSchramm.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BenjaminiSchramm.lean; bytes 8569..9115
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_BenjaminiSchramm

namespace OAI

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

namespace Percolation.BenjaminiSchramm

universe u v

/-- Nonuniqueness for every prescribed finite symmetric Cayley generating set. -/
theorem cayley_main {Λ : Type u} [Group Λ]
    (S : Finset Λ) (hsym : ∀ s ∈ S, s⁻¹ ∈ S) (_hone : 1 ∉ S)
    (hgen : Subgroup.closure (S : Set Λ) = ⊤) (hna : ¬ FolnerAmenable Λ) :
    OperatorBounded (cayleyBond S) (pc (cayleyBond S)) ∧
      MainConclusion (cayleyBond S) ∧
      ∀ p : unitInterval, pc (cayleyBond S) < p → p < pu (cayleyBond S) →
        ∀ᵐ ω ∂law p, (infiniteClusters (cayleyBond S) ω).Infinite := by
  sorry

end Percolation.BenjaminiSchramm
end OAI
