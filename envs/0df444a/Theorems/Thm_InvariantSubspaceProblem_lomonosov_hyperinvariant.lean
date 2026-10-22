-- Prove2me | Theorems.Thm_InvariantSubspaceProblem_lomonosov_hyperinvariant
-- name    : InvariantSubspaceProblem.lomonosov_hyperinvariant
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T17:24:31.432253+00:00
-- url     : https://prove2.me/theorems/14dd1b3d-dfd5-493e-8e5d-9e25c3eea5da
-- title:
--   Lomonosov: non-zero compact operators have hyperinvariant subspaces
-- statement:
--   **Theorem (Lomonosov 1973).** Let $E$ be an infinite-dimensional complex Banach space and let $K\colon E\to E$ be a non-zero compact operator. Then $K$ has a non-trivial closed hyperinvariant subspace: there is a closed subspace $S$ with $\{0\}\neq S\neq E$ such that $A(S)\subseteq S$ for every bounded operator $A$ with $AK=KA$.
--
--   This strengthens the Aronszajn–Smith theorem and is the main result of Lomonosov's paper.
-- source:
--   V. I. Lomonosov, Invariant subspaces for the family of operators which commute with a completely continuous operator, Funct. Anal. Appl. 7 (1973) 213–214, https://doi.org/10.1007/BF01080698 , main theorem.

import Definitions.Def_InvariantSubspaceProblem_Defs

namespace InvariantSubspaceProblem

theorem lomonosov_hyperinvariant (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (hinf : ¬ FiniteDimensional ℂ E)
    (K : E →L[ℂ] E) (hK : IsCompactOperator K) (hK0 : K ≠ 0) :
    HasNontrivialClosedHyperinvariantSubspace K := by sorry

end InvariantSubspaceProblem
