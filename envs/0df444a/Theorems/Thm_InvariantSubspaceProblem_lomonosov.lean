-- Prove2me | Theorems.Thm_InvariantSubspaceProblem_lomonosov
-- name    : InvariantSubspaceProblem.lomonosov
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T17:25:02.531002+00:00
-- url     : https://prove2.me/theorems/5fd3baa2-4af7-49e1-bcf2-0c51cc14f599
-- title:
--   Lomonosov: operators commuting with a compact operator
-- statement:
--   **Theorem (Lomonosov 1973).** Let $E$ be an infinite-dimensional complex Banach space and let $T\colon E\to E$ be a bounded operator. If $T$ commutes with some non-zero compact operator $K$ (i.e. $TK=KT$), then $T$ has a non-trivial closed invariant subspace.
--
--   This is the form in which Lomonosov's theorem is usually quoted; it covers, for example, all operators that are polynomially compact.
-- source:
--   V. I. Lomonosov, Invariant subspaces for the family of operators which commute with a completely continuous operator, Funct. Anal. Appl. 7 (1973) 213–214, https://doi.org/10.1007/BF01080698 , consequence of the main theorem.

import Definitions.Def_InvariantSubspaceProblem_Defs

namespace InvariantSubspaceProblem

theorem lomonosov (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (hinf : ¬ FiniteDimensional ℂ E) (T K : E →L[ℂ] E) (hK : IsCompactOperator K)
    (hK0 : K ≠ 0) (hTK : T * K = K * T) :
    HasNontrivialClosedInvariantSubspace T := by sorry

end InvariantSubspaceProblem
