-- Prove2me | Theorems.Thm_OAI_CrouzeixHilbert_hilbert
-- name    : OAI.CrouzeixHilbert.hilbert
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:31.164641+00:00
-- url     : https://prove2.me/theorems/37a8ad83-c43a-49ec-8079-0b0bb960fc01
-- statement:
--   The theorem states that, for every complex Hilbert space H (complete inner product space over ℂ, in any universe) and every bounded linear operator A on H, three things hold. First, if H is nontrivial, then the numerical range W(A)={⟨x,Ax⟩ : ‖x‖=1} has compact, convex closure W̄, the spectrum of A lies in W̄, and a sharp Crouzeix-type calculus holds with constant 2 for matrix-valued functions with m×m complex coefficients, m>0. For matrix polynomials p(z)=Σ_{k≤d} z^k B_k, the amplified operator Σ A^k⊗B_k (acting on the completed tensor product of H with ℂ^m) has norm at most 2 sup_{W(A)}‖p‖, where the supremum is taken together with 0; moreover this supremum over W(A) equals that over W̄, and is attained at some point of W̄. For an open set U containing W̄ and a matrix function F with entrywise holomorphic entries on U, a smooth closed contour in U minus W̄ with winding number 1 about points of W̄ and 0 about points outside U exists; every such contour gives, entry by entry, the same Cauchy-integral functional calculus value as the holomorphic evaluation; the assembled operator has norm at most 2 sup_{W̄}‖F‖; and that supremum is attained on W̄. For a matrix of rational functions whose denominators do not vanish on W̄, each denominator evaluated at A is invertible, the rational evaluation has norm at most 2 sup_{W̄}‖R‖ with the supremum attained on W̄, and it agrees with the holomorphic evaluation on some open neighborhood U of W̄ on which R is entrywise holomorphic. Second, if H is a subsingleton, then the numerical range is empty and all polynomial, holomorphic and rational evaluations (for every m, d, U, F, R, without side conditions) are zero, with zero supremum, so the factor-2 inequality holds trivially. Third, the constant 2 is sharp: there exist an operator on ℂ² and a degree-one scalar polynomial with coefficients B₀, B₁ whose supremum over the numerical range is 1 while the amplified operator norm equals 2.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CrouzeixHilbert.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CrouzeixHilbert.lean; bytes 6277..6516
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_CrouzeixHilbert

namespace OAI

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace

open Set

namespace CrouzeixHilbert

universe u

theorem hilbert (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : Operator H) :
    (Nontrivial H → NonzeroConclusion A) ∧
    (Subsingleton H → ZeroConclusion A) ∧ SharpConstant := by
  sorry

end CrouzeixHilbert
end
end OAI
