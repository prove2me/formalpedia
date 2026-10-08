-- Prove2me | Theorems.Thm_OAI_KLInvariance_combinatorial_invariance
-- name    : OAI.KLInvariance.combinatorial_invariance
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:49.424775+00:00
-- url     : https://prove2.me/theorems/3d1ef12e-e054-4519-a443-866b4f042c52
-- statement:
--   The theorem states that, for two Coxeter systems cs on a group W with Coxeter matrix M and cs' on a possibly different group W' with Coxeter matrix M' (with arbitrary index types and universes), if u ≤ b in the strong Bruhat order of cs and u' ≤ b' in the strong Bruhat order of cs', and there is an order isomorphism ι between the Bruhat intervals [u,b] in W and [u',b'] in W', then the two Kazhdan–Lusztig polynomials agree: klPolynomial(cs,u,b) = klPolynomial(cs',u',b') in ℤ[X]. Here the strong Bruhat order is the reflexive-transitive closure of the relation x → y that holds when the Coxeter length of x is strictly less than that of y and y = t·x for some reflection t. An interval [u,b] is the set of x with u ≤ x ≤ b, ordered by the restricted Bruhat order. The polynomial klPolynomial(cs,x,y) is the second component P of a pair of polynomial families (R,P) chosen by Classical.epsilon among those satisfying the normalization: R(x,x)=1 and P(x,x)=1; R and P vanish unless x ≤ y; R satisfies a recursion in a simple generator s with length(s·y)<length(y), equal to R(s·x,s·y) when s·x is shorter than x and otherwise (X−1)R(x,s·y)+X·R(s·x,s·y); for x<y, 2·deg P(x,y) is less than length(y)−length(x); and for x ≤ y, X^d P(x,y)(1/X), with d the length difference, equals the finite sum over z in [x,y] of R(x,z)P(z,y). This is the combinatorial invariance statement, and the theorem is admitted in the source rather than proved.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/KLInvariance.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/KLInvariance.lean; bytes 3453..3810
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_KLInvariance

namespace OAI

namespace KLInvariance

universe u v u' v'

variable {B : Type u} {W : Type v} [Group W] {M : CoxeterMatrix B}

theorem combinatorial_invariance
    {B' : Type u'} {W' : Type v'} [Group W'] {M' : CoxeterMatrix B'}
    (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W')
    {u b : W} {u' b' : W'}
    (hub : BruhatLE cs u b) (hub' : BruhatLE cs' u' b')
    (ι : Interval cs u b ≃o Interval cs' u' b') :
    klPolynomial cs u b = klPolynomial cs' u' b' := by
  sorry

end KLInvariance
end OAI
