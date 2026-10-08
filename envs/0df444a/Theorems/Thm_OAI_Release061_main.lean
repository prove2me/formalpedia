-- Prove2me | Theorems.Thm_OAI_Release061_main
-- name    : OAI.Release061.main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:15.629984+00:00
-- url     : https://prove2.me/theorems/4c25161b-f432-4c58-a691-b1c853a32be8
-- statement:
--   The theorem states that, for a natural number n, take V a complex affine algebraic set in ℂⁿ (the common zero set of some family of complex polynomials) and U a subset of V that is open in V's subspace topology, connected, semialgebraic, and bounded. Semialgebraic here means U lies in the smallest class of subsets of ℂⁿ, viewed as ℝ²ⁿ via real and imaginary parts, that contains the zero sets and strict positivity sets of real polynomials in those coordinates and is closed under complement and binary union. Let Γ be a discrete topological group acting on U with a proper action such that the orbit space is compact, and suppose every element γ acts by a holomorphic map, meaning that near each point of U the map p ↦ γ·p agrees on U with a complex-analytic map defined on an open neighborhood in ℂⁿ. Then U is smooth, meaning each point has a neighborhood W in U, open in U, that is biholomorphic (a homeomorphism that is holomorphic in both directions in the same local-analytic sense) to an open subset of some ℂᵐ. Moreover, there exist m and a set D in ℂᵐ that is a bounded symmetric domain, meaning D is open, connected and bounded and each point p of D has a biholomorphic involution of D fixing p and having p as an isolated fixed point, such that U is biholomorphic to D.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SymmetricDomains.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SymmetricDomains.lean; bytes 2050..2678
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_SymmetricDomains

namespace OAI

namespace Release061

theorem main {n : ℕ} (V U : Set (Affine n))
    (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hopen : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    (hconn : IsConnected U) (hsa : IsSemialgebraic U)
    (hbounded : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) :
    IsSmooth U ∧ ∃ (m : ℕ) (D : Set (Affine m)),
      IsBoundedSymmetricDomain D ∧ Nonempty (Biholomorph U D) := by
  sorry

end Release061
end OAI
