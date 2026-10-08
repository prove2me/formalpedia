-- Prove2me | Theorems.Thm_KleinbergHITS_Conv_principal_eigenvector_nonneg
-- name    : KleinbergHITS.Conv.principal_eigenvector_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:19:19.087298+00:00
-- url     : https://prove2.me/theorems/66cbfd28-cf07-4581-9421-0ee9a3287d13
-- title:
--   §3, proof of Theorem 3.1, p. 11 — if M has only non-negative entries, its principal eigenvector has only non-negative entries
-- statement:
--   Let $M$ be a real symmetric $n\times n$ matrix with only non-negative entries, $M_{ij}\ge0$, and suppose $M$ satisfies Assumption (†) (its eigenvalue $\lambda_1$ of largest absolute value is simple, nonzero, and strictly larger in absolute value than every other eigenvalue). Then $M$ has a principal eigenvector $\omega_1$ — a unit vector spanning the eigenspace of $\lambda_1$ — with
--   $$\omega_1(i)\ge0\qquad\text{for all } i.$$
--
--   The proof of Theorem 3.1 uses this "corollary" to show that the starting vectors $z$ and $A^{\top}z$ are not orthogonal to the principal eigenvectors of $AA^{\top}$ and $A^{\top}A$.
--
--   **Formalization Note** The principal eigenvector is determined only up to sign, so "the principal eigenvector has only non-negative entries" is stated as: one of the two unit vectors spanning the principal eigenspace has non-negative entries (the other then has non-positive entries). Assumption (†) is the standing assumption of the page, under which "the principal eigenvector" is defined.
-- source:
--   Kleinberg, Authoritative sources in a hyperlinked environment, J. ACM 46(5) (1999), author's copy, p. 11, §3, proof of Theorem 3.1, second paragraph ("Also (as a corollary), if M has only non-negative entries, then the principal eigenvector of M has only non-negative entries")

import Mathlib
import Definitions.Def_KleinbergHITS_Conv_Setting

namespace KleinbergHITS.Conv

open Matrix

/-- Kleinberg (1999), §3, proof of Theorem 3.1, p. 11: "if M has only non-negative entries, then the
principal eigenvector of M has only non-negative entries" — for a symmetric `M` satisfying
Assumption (†), the principal eigenvector can be chosen (by its sign) with non-negative entries. -/
theorem principal_eigenvector_nonneg {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm)
    (hnn : ∀ i j, 0 ≤ M i j) (hD : Dagger M) :
    ∃ ω, IsPrincipalEigenvector M ω ∧ ∀ i, 0 ≤ ω i := by sorry

end KleinbergHITS.Conv
