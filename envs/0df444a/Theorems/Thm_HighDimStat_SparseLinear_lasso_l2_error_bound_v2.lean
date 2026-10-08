-- Prove2me | Theorems.Thm_HighDimStat_SparseLinear_lasso_l2_error_bound_v2
-- name    : HighDimStat.SparseLinear.lasso_l2_error_bound_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:20:35.610103+00:00
-- url     : https://prove2.me/theorems/e96fc9b7-f63b-45c1-8192-e727387b7eb5
-- title:
--   The Lagrangian Lasso's $\ell_2$-error bound under the restricted eigenvalue condition (Theorem 7.13(a), $\lambda_n>0$)
-- statement:
--   **Theorem 7.13(a) and final sentence.** Under a hard-sparsity assumption on the true
--   parameter and a curvature (restricted eigenvalue) assumption on the design, every solution
--   of the Lagrangian Lasso with a large-enough regularization parameter is within a
--   computable $\ell_2$-distance of the truth, and its $\ell_1$-error is controlled by that
--   same $\ell_2$-error.
--
--   Fix $X \in \mathbb R^{n\times d}$, $w \in \mathbb R^n$ (the noise), $\theta^*, \hat\theta
--   \in \mathbb R^d$, $S \subseteq \{1,\dots,d\}$ (the support of $\theta^*$, with $|S|=s$),
--   and $\kappa, \lambda_n \in \mathbb R$ with $\kappa > 0$ and $\lambda_n > 0$. Assume:
--
--   - (A1) $\theta^*$ is supported on $S$;
--   - (A2) $X$ satisfies the restricted eigenvalue condition over $S$ with parameters
--     $(\kappa, 3)$;
--   - $\lambda_n \ge 2\|X^Tw/n\|_\infty$;
--   - $\hat\theta$ solves the Lagrangian Lasso (7.18), $\min_\theta \frac{1}{2n}\|y-X\theta\|_2^2 + \lambda_n\|\theta\|_1$, for $y = X\theta^*+w$.
--
--   Then
--
--   $$
--   \|\hat\theta - \theta^*\|_2 \;\le\; \frac{3}{\kappa}\sqrt{s}\,\lambda_n, \qquad
--   \|\hat\theta - \theta^*\|_1 \;\le\; 4\sqrt{s}\,\|\hat\theta - \theta^*\|_2.
--   $$
--
--   This is the chapter's title result: a deterministic guarantee that holds for *any* Lasso
--   solution, any noise vector, and any design matrix satisfying the restricted eigenvalue
--   condition.
--
--   **Formalization Note.** The retired version (`lasso_l2_error_bound`) did not require the
--   regularization parameter to be positive, so at $\lambda_n = 0$ (allowed by
--   $\lambda_n \ge 2\|X^Tw/n\|_\infty$ when $w = 0$) the "Lasso" is unpenalized least squares and
--   the bound $\|\hat\theta-\theta^*\|_2 \le 0$ fails (accepted disproof with $n=1$, $d=2$). The
--   new statement adds `hlam_pos : 0 < lam`: the Lagrangian Lasso program (7.18) is defined with
--   $\lambda_n > 0$, and the proof uses $\lambda_n>0$ to pass from the basic inequality to the cone
--   condition $\hat\Delta\in\mathbb C_3(S)$. Only part (a) of Theorem 7.13 is formalized (as
--   before); $\kappa>0$ is made explicit as in the retired version; the $\ell_1$-bound of the
--   final sentence is kept as the second conjunct. No other hypothesis changed: $n$ and $d$ are
--   arbitrary naturals (at $n = 0$ or $d = 0$ the statement is vacuous or trivially true).
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
parameters `(κ, 3)`: any solution `θhat` of the Lagrangian Lasso (7.18) — a program whose
regularization parameter is **positive**, `λₙ > 0` — observing `y = Xθ* + w`, with
`λₙ ≥ 2‖Xᵀw/n‖∞`, satisfies `‖θhat − θ*‖₂ ≤ (3/κ)√s λₙ`; in addition,
`‖θhat − θ*‖₁ ≤ 4√s‖θhat − θ*‖₂`.

Correction relative to the retired version: the positivity `0 < λₙ` of the regularization
parameter (part of the definition of program (7.18), and used in the proof to pass from the
basic inequality to the cone condition `Δ̂ ∈ C₃(S)`) was missing; at `λₙ = 0` the program is
unpenalized least squares and the bound fails. -/
theorem lasso_l2_error_bound_v2 {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ)
    (θstar θhat : Fin d → ℝ) (S : Finset (Fin d)) (κ lam : ℝ)
    (hSupport : HasSupport θstar S)
    (hκ : 0 < κ)
    (hRE : RestrictedEigenvalue X S κ 3)
    (hlam_pos : 0 < lam)
    (hlam : 2 * linfNorm (fun j => X.transpose.mulVec w j / (n : ℝ)) ≤ lam)
    (hsol : IsLagrangianLassoSolution X (X.mulVec θstar + w) lam θhat) :
    Real.sqrt (∑ j, (θhat j - θstar j) ^ 2) ≤ (3 / κ) * Real.sqrt (S.card : ℝ) * lam ∧
    l1Norm (fun j => θhat j - θstar j) ≤
      4 * Real.sqrt (S.card : ℝ) * Real.sqrt (∑ j, (θhat j - θstar j) ^ 2) := by sorry

end HighDimStat.SparseLinear
