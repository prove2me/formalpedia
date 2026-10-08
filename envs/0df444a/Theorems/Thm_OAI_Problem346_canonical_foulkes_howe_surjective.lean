-- Prove2me | Theorems.Thm_OAI_Problem346_canonical_foulkes_howe_surjective
-- name    : OAI.Problem346.canonical_foulkes_howe_surjective
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:10.490217+00:00
-- url     : https://prove2.me/theorems/84954022-825d-4d39-b112-081887d21f62
-- statement:
--   The theorem states that, for every finite-dimensional complex vector space V and all natural numbers a and b with a ≥ 2 and a(a−1) ≤ b, there is a ℂ-linear map μ from Sym^b(Sym^a V) to Sym^a(Sym^b V) that satisfies the Foulkes condition, is surjective, and is the only linear map satisfying that condition. Here Sym^n V is the span, inside the symmetric algebra of V over ℂ, of the products v₀⋯v_{n−1} of n elements of V, and the symbol [v₀,…,v_{n−1}] denotes such a monomial regarded as an element of Sym^n V. A linear map μ satisfies the Foulkes condition when, for every array v of b rows and a columns of vectors v_{j,i} in V, μ sends the monomial [[v_{0,0},…,v_{0,a−1}], …, [v_{b−1,0},…,v_{b−1,a−1}]] in Sym^b(Sym^a V), whose inner monomials are the rows, to (1/(a!)^b) times the sum, over all b-tuples (σ₀,…,σ_{b−1}) of permutations of the a column positions, of the monomial in Sym^a(Sym^b V) whose i-th entry is the monomial [v_{0,σ₀(i)}, …, v_{b−1,σ_{b−1}(i)}], for i from 0 to a−1.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/FoulkesHowe.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/FoulkesHowe.lean; bytes 1376..1778
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_FoulkesHowe

namespace OAI

noncomputable section

open scoped BigOperators

universe u

namespace Problem346

theorem canonical_foulkes_howe_surjective :
    ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a b : ℕ), 2 ≤ a → a * (a - 1) ≤ b → ∃ μ : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V), IsFoulkesMap a b V μ ∧ Function.Surjective μ ∧ ∀ ν : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V), IsFoulkesMap a b V ν → ν = μ := by
  sorry

end Problem346
end
end OAI
