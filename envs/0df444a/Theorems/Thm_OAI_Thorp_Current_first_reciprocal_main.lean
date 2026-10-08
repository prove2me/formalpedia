-- Prove2me | Theorems.Thm_OAI_Thorp_Current_first_reciprocal_main
-- name    : OAI.Thorp.Current.first_reciprocal_main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:30.814998+00:00
-- url     : https://prove2.me/theorems/16d7d50d-a327-4588-a311-91d91eadec19
-- statement:
--   The theorem states a conjunction of two parts. First, for each n let reciprocalFirst(n) be the sum, over all partitions p of n, of 1/deg(p), where deg(p) is the complex dimension of the Specht module of shape p (the span of the permutation-group translates of the polytabloid built from the canonical tableau, inside the space of tabloids). Let C1 be the supremum of reciprocalFirst(n) over n ≥ 1. The theorem asserts that this set of values is bounded above, that reciprocalFirst(n) ≤ C1 for every n ≥ 1, and that exceptionalFirst(n) tends to 0 as n → ∞, where exceptionalFirst(n) is the same sum of 1/deg(p) restricted to partitions p whose defect n − max(first row length, first column length) is positive. Second, for every d ≥ 3, every bijection e between the set of positions {0,1}^d (functions Fin d → Bool) and Fin 8 × Fin(2^(d−3)), every finite-dimensional complex inner product space E, and every irreducible complex representation ρ of the symmetric group on the positions, acting on E by inner-product-preserving maps, the following holds. Let ν be a probability distribution on this symmetric group (nonnegative values summing to 1) such that, for each i in Fin 8 and each group element g, the total ν-mass of the coset g·B_i is at most 4·|Sym(2^(d−3))|/|Sym(positions)|, where B_i is the subgroup of permutations that act through e by an arbitrary permutation of the i-th block of 2^(d−3) points and fix all other points. Then the operator norm of Σ_g ν(g)ρ(g) is at most √(32·C1)·(dim E)^(−5/16).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ThorpFirstReciprocal.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ThorpFirstReciprocal.lean; bytes 7103..8230
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_ThorpFirstReciprocal

namespace OAI

noncomputable section

universe uG uV uE uX uH uI uβ uα

open scoped BigOperators Classical ComplexConjugate InnerProductSpace

open Filter Topology

namespace Thorp

namespace Current

theorem first_reciprocal_main :
    (BddAbove (Set.range (fun n : {n : ℕ // 1 ≤ n} => reciprocalFirst n.val)) ∧
    (∀ n : ℕ, 1 ≤ n → reciprocalFirst n ≤ C1) ∧
    Tendsto exceptionalFirst atTop (nhds 0)) ∧
    (∀ (d : ℕ) (_hd : 3 ≤ d)
    (e : Position d ≃ Fin 8 × Fin (2 ^ (d - 3)))
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (ρ : Representation ℂ (Equiv.Perm (Position d)) E)
    [Representation.IsIrreducible ρ]
    (_ : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (ν : Equiv.Perm (Position d) → ℝ)
    (_ : ∀ g, 0 ≤ ν g) (_ : ∑ g, ν g = 1)
    (_ : ∀ (i : Fin 8) (g : Equiv.Perm (Position d)),
      ∑ h : Equiv.Perm (Fin (2 ^ (d - 3))),
          ν (g * Block.embedding e (Pi.mulSingle i h)) ≤
        4 * (Fintype.card (Equiv.Perm (Fin (2 ^ (d - 3)))) : ℝ) /
          Fintype.card (Equiv.Perm (Position d))),
    ‖LinearMap.toContinuousLinearMap (Fourier.integrated ρ (fun g => (ν g : ℂ)))‖ ≤
      Real.sqrt (32 * C1) * (Module.finrank ℂ E : ℝ) ^ (-5 / 16 : ℝ)) := by
  sorry

end Current
end Thorp
end
end OAI
