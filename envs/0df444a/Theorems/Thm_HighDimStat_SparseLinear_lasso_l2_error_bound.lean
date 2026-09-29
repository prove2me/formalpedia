-- Prove2me | Theorems.Thm_HighDimStat_SparseLinear_lasso_l2_error_bound
-- name    : HighDimStat.SparseLinear.lasso_l2_error_bound
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T23:10:50.927392+00:00
-- url     : https://prove2.me/theorems/42e19890-18ba-41a0-bb9b-0dc7f1ca8a42
-- title:
--   The Lagrangian Lasso's l2-error bound under the restricted eigenvalue condition
-- statement:
--   **Theorem 7.13(a) and final sentence.** Under a hard-sparsity assumption on the true
--   parameter and a curvature (restricted eigenvalue) assumption on the design, every solution
--   of the Lagrangian Lasso with a large-enough regularization parameter is within a
--   computable $\ell_2$-distance of the truth, and its $\ell_1$-error is controlled by that
--   same $\ell_2$-error.
--
--   Fix $X \in \mathbb R^{n\times d}$, $w \in \mathbb R^n$ (the noise), $\theta^*, \hat\theta
--   \in \mathbb R^d$, $S \subseteq \{1,\dots,d\}$ (the support of $\theta^*$, with $|S|=s$),
--   and $\kappa, \lambda_n \in \mathbb R$ with $\kappa > 0$. Assume:
--
--   - (A1) $\theta^*$ is supported on $S$;
--   - (A2) $X$ satisfies the restricted eigenvalue condition over $S$ with parameters
--     $(\kappa, 3)$;
--   - $\lambda_n \ge 2\|X^Tw/n\|_\infty$;
--   - $\hat\theta$ solves the Lagrangian Lasso (7.18) for $(X,\, X\theta^*+w,\, \lambda_n)$.
--
--   Then
--
--   $$
--   \|\hat\theta - \theta^*\|_2 \;\le\; \frac{3}{\kappa}\sqrt{s}\,\lambda_n, \qquad
--   \|\hat\theta - \theta^*\|_1 \;\le\; 4\sqrt{s}\,\|\hat\theta - \theta^*\|_2.
--   $$
--
--   This is the chapter's title result: a deterministic (non-probabilistic) guarantee that
--   holds for *any* Lasso solution, any noise vector, and any design matrix satisfying the
--   restricted eigenvalue condition — the source of every subsequent probabilistic corollary
--   in the chapter, once the restricted eigenvalue condition and the bound on $\lambda_n$ are
--   verified for a specific statistical model.
--
--   **Formalization Note** Only part (a) of Theorem 7.13 (the Lagrangian Lasso) is formalized;
--   parts (b) (constrained Lasso) and (c) (relaxed basis pursuit) are left out of this
--   mission's scope (see `description.md`). The hypothesis $\kappa > 0$ is not spelled out
--   in Definition 7.12 itself but is used throughout the book's discussion of Theorem 7.13
--   (division by $\kappa$ in every bound) and is made explicit here. The final-sentence
--   $\ell_1$-bound is included as a second conjunct of the conclusion, not dropped as a
--   corollary, per this book's chapter-specific pitfall.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 210 (PDF p. 230), Theorem 7.13(a), Eq. (7.25a)

import Mathlib
import Definitions.Def_HighDimStat_SparseLinear_HasSupport
import Definitions.Def_HighDimStat_SparseLinear_RestrictedEigenvalue
import Definitions.Def_HighDimStat_SparseLinear_IsLagrangianLassoSolution
import Definitions.Def_HighDimStat_SparseLinear_L1Norm
import Definitions.Def_HighDimStat_SparseLinear_LInftyNorm

namespace HighDimStat.SparseLinear

/-- **Theorem 7.13(a)**, Wainwright, *High-Dimensional Statistics* (2019), Eq. (7.25a) and the
final sentence, p. 210. Under (A1) `θ*` is supported on `S ⊆ {1,...,d}` with `|S| = s`, and
(A2) the design matrix `X` satisfies the restricted eigenvalue condition over `S` with
parameters `(κ, 3)`: any solution `θhat` of the Lagrangian Lasso (7.18), observing
`y = Xθ* + w`, with regularization parameter `λₙ ≥ 2‖Xᵀw/n‖∞`, satisfies
`‖θhat − θ*‖₂ ≤ (3/κ)√s λₙ`; in addition, `‖θhat − θ*‖₁ ≤ 4√s‖θhat − θ*‖₂`. -/
theorem lasso_l2_error_bound {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ)
    (θstar θhat : Fin d → ℝ) (S : Finset (Fin d)) (κ lam : ℝ)
    (hSupport : HasSupport θstar S)
    (hκ : 0 < κ)
    (hRE : RestrictedEigenvalue X S κ 3)
    (hlam : 2 * linfNorm (fun j => X.transpose.mulVec w j / (n : ℝ)) ≤ lam)
    (hsol : IsLagrangianLassoSolution X (X.mulVec θstar + w) lam θhat) :
    Real.sqrt (∑ j, (θhat j - θstar j) ^ 2) ≤ (3 / κ) * Real.sqrt (S.card : ℝ) * lam ∧
    l1Norm (fun j => θhat j - θstar j) ≤
      4 * Real.sqrt (S.card : ℝ) * Real.sqrt (∑ j, (θhat j - θstar j) ^ 2) := by sorry

end HighDimStat.SparseLinear
