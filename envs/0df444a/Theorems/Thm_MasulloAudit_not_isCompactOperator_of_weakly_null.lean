-- Prove2me | Theorems.Thm_MasulloAudit_not_isCompactOperator_of_weakly_null
-- name    : MasulloAudit.not_isCompactOperator_of_weakly_null
-- status  : Proved
-- author  : @deleted
-- created : 2026-11-21T00:29:33.52628+00:00
-- url     : https://prove2.me/theorems/91b69d8e-9d25-4612-ad49-d80b4fbc6304
-- title:
--   Compact operators send bounded weakly null sequences to norm-null sequences
-- statement:
--   Let $\mathbb K\in\{\mathbb R,\mathbb C\}$ and let $E$, $F$ be Hilbert spaces over $\mathbb K$ (complete inner product spaces, inner product $\langle\cdot,\cdot\rangle$ conjugate-linear in the first slot). Let $T:E\to F$ be a bounded linear operator, and let $(x_n)_{n\in\mathbb N}$ be a sequence in $E$ such that:
--
--   1. $(x_n)$ is bounded: $\|x_n\|\le R$ for all $n$, for some $R\in\mathbb R$;
--   2. $(x_n)$ is weakly null: $\langle y, x_n\rangle\to 0$ as $n\to\infty$ for every $y\in E$;
--   3. the images stay uniformly away from $0$: there is $c>0$ such that $\|T x_n\|\ge c$ for all sufficiently large $n$.
--
--   Then $T$ is not compact:
--   $$
--   \sup_n\|x_n\|<\infty,\quad x_n\rightharpoonup 0,\quad \liminf_{n\to\infty}\|Tx_n\|\ge c>0 \;\Longrightarrow\; T \text{ is not a compact operator}.
--   $$
--
--   Equivalently, a compact operator between Hilbert spaces maps bounded weakly null sequences to norm-null sequences. This is the standard criterion for proving non-compactness: one exhibits an explicit weakly null sequence (for instance an orthonormal sequence escaping to infinity) whose images do not shrink in norm. It is the abstract ingredient used to show that truncated convolution operators on $\ell^2(\mathbb Z)$ are not compact.
--
--   **Formalization Note.** The field is any `RCLike 𝕜`; $E$ and $F$ are `InnerProductSpace 𝕜` with `CompleteSpace`, and $T$ is `E →L[𝕜] F`. Compactness is Mathlib's `IsCompactOperator T` (the image of some neighbourhood of $0$ is relatively compact). Weak nullity is stated directly as convergence of `inner 𝕜 y (x n)` to $0$ for every $y$, and condition 3 is an `∀ᶠ n in atTop` statement.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, footnote 2 on p. 514 and the operator R_ρ A_φ̃ = P_{ρ,λ} ∘ A_φ̃ ∘ P̂_{ρ,λ′} on pp. 516-517; cf. A. Connes, Selecta Math. 5 (1999), §VII.

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Compact.Basic

open Filter Topology

namespace MasulloAudit

theorem not_isCompactOperator_of_weakly_null {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    {T : E →L[𝕜] F} {x : ℕ → E} {R c : ℝ}
    (hb : ∀ n, ‖x n‖ ≤ R)
    (hw : ∀ y : E, Tendsto (fun n => (inner 𝕜 y (x n) : 𝕜)) atTop (𝓝 0))
    (hc0 : 0 < c) (hc : ∀ᶠ n in atTop, c ≤ ‖T (x n)‖) :
    ¬ IsCompactOperator T := by sorry

end MasulloAudit
