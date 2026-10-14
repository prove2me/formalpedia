-- Prove2me | Theorems.Thm_InvariantSubspaceProblem_aronszajn_smith
-- name    : InvariantSubspaceProblem.aronszajn_smith
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T17:23:55.899007+00:00
-- url     : https://prove2.me/theorems/830f6aba-5325-49ba-a20e-94ea8667d32b
-- title:
--   Aronszajn–Smith: compact operators have closed invariant subspaces
-- statement:
--   **Theorem (von Neumann; Aronszajn–Smith 1954).** Let $\mathbb{K}\in\{\mathbb{R},\mathbb{C}\}$, let $E$ be an infinite-dimensional Banach space over $\mathbb{K}$, and let $K\colon E\to E$ be a compact operator. Then $K$ has a non-trivial closed invariant subspace.
--
--   This was the first major positive result on the invariant subspace problem (von Neumann's unpublished Hilbert-space argument, published and extended to Banach spaces by Aronszajn and Smith).
--
--   **Formalization Note** The scalar field ranges over Mathlib's `RCLike`, covering both real and complex scalars; compactness is Mathlib's `IsCompactOperator`.
-- source:
--   N. Aronszajn & K. T. Smith, Invariant subspaces of completely continuous operators, Ann. of Math. 60 (1954) 345–350, https://doi.org/10.2307/1969637 , main theorem.

import Definitions.Def_InvariantSubspaceProblem_Defs

namespace InvariantSubspaceProblem

theorem aronszajn_smith {𝕜 : Type*} [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [CompleteSpace E] (hinf : ¬ FiniteDimensional 𝕜 E)
    (K : E →L[𝕜] E) (hK : IsCompactOperator K) :
    HasNontrivialClosedInvariantSubspace K := by sorry

end InvariantSubspaceProblem
