-- Prove2me | Theorems.Thm_HighDimStat_Rkhs_exists_countable_hilbertBasis_eigenvectors
-- name    : HighDimStat.Rkhs.exists_countable_hilbertBasis_eigenvectors
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-31T11:06:14.594877+00:00
-- url     : https://prove2.me/theorems/9c3d5c99-3e94-4150-8c25-fa64aca8f361
-- title:
--   Countable Hilbert basis of eigenvectors for compact self-adjoint operators
-- statement:
--   For any compact self-adjoint continuous linear operator $T : E \to E$ on a separable real Hilbert space $E$, there exists a countable index type $\iota$, a Hilbert basis $(b_j)_{j \in \iota}$ of $E$, and real eigenvalues $(\mu_j)_{j \in \iota}$ such that $T(b_j) = \mu_j b_j$ for every $j \in \iota$.
-- source:
--   Wainwright, High-Dimensional Statistics (2019), Section 12.4.1 (Mercer's theorem spectral step), p. 398

import Mathlib
open scoped InnerProductSpace

namespace HighDimStat.Rkhs

/-- Spectral theorem for compact self-adjoint operators on a separable real Hilbert space:
there is a countable Hilbert basis consisting of eigenvectors. -/
theorem exists_countable_hilbertBasis_eigenvectors
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (T : E →L[ℝ] E) (hT : IsCompactOperator T) (hsym : (T : E →ₗ[ℝ] E).IsSymmetric) :
    ∃ (ι : Type) (_ : Countable ι) (b : HilbertBasis ι ℝ E) (μ : ι → ℝ),
      ∀ j, T (b j) = μ j • b j := by sorry

end HighDimStat.Rkhs
