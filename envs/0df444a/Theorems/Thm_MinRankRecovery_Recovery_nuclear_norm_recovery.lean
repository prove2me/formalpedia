-- Prove2me | Theorems.Thm_MinRankRecovery_Recovery_nuclear_norm_recovery
-- name    : MinRankRecovery.Recovery.nuclear_norm_recovery
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:18:19.270975+00:00
-- url     : https://prove2.me/theorems/6f5dfce8-5ec0-4440-a6b8-d06bf87b008d
-- title:
--   Theorem 3.3 — if δ_5r < 1/10, nuclear norm minimization recovers X₀ exactly
-- statement:
--   Let $\mathcal A:\mathbb R^{m\times n}\to\mathbb R^p$ be a linear map with restricted isometry constants $\delta_r=\delta_r(\mathcal A)$ (Definition 3.1), let $r\ge1$ be an integer, and let $X_0\in\mathbb R^{m\times n}$ have rank at most $r$. Put $b=\mathcal A(X_0)$ and consider the convex program
--   $$X^*:=\arg\min_X\ \|X\|_*\quad\text{s.t.}\quad\mathcal A(X)=b. \tag{3.1}$$
--   If
--   $$\delta_{5r}<\tfrac1{10},$$
--   then $X^*=X_0$: every matrix $X$ with $\mathcal A(X)=b$ and $\|X\|_*\le\|X_0\|_*$ equals $X_0$. In particular $X_0$ is the unique minimizer of (3.1).
--
--   This is the paper's main deterministic recovery guarantee: a restricted isometry condition on the measurement map, with an absolute constant independent of $m,n,r,p$, ensures that the tractable convex relaxation recovers every matrix of rank at most $r$ exactly. Section 4 of the paper shows that many random maps satisfy the condition with $p$ of order $r(m+n)\log(mn)$.
--
--   **Formalization Note** The conclusion is phrased so that it does not depend on how an arg min is chosen: since $X_0$ is itself feasible, "every feasible $X$ with $\|X\|_*\le\|X_0\|_*$ equals $X_0$" says exactly that $X_0$ is the unique minimizer. The paper's setting takes $\operatorname{rank}X_0=r$; here $\operatorname{rank}X_0\le r$, which is equivalent because $\delta_{5r'}\le\delta_{5r}$ for $r'\le r$. The constant $\delta_r$ is defined for every $r$ (the paper restricts to $1\le r\le m$ under $m\le n$); $m\le n$, $p\ge1$ and $X_0\ne0$ are not assumed.
-- source:
--   Recht, Fazel & Parrilo, arXiv:0706.4138v1, Theorem 3.3, p. 12 (problem (3.1), p. 11)

import Mathlib
import Definitions.Def_HighDimStat_MatrixRank_Core
import Definitions.Def_MinRankRecovery_Recovery_ripConst

open HighDimStat.MatrixRank Matrix

namespace MinRankRecovery.Recovery

/-- Theorem 3.3, p. 12: if `r ≥ 1` and `δ_5r < 1/10`, then for every `X₀` of rank at most `r`,
`X₀` is the unique minimizer of `‖X‖_*` subject to `𝒜(X) = 𝒜(X₀)`: every feasible `X` with
`‖X‖_* ≤ ‖X₀‖_*` equals `X₀`. -/
theorem nuclear_norm_recovery {m n p : ℕ} (Xs : Fin p → Matrix (Fin m) (Fin n) ℝ) (r : ℕ)
    (hr : 1 ≤ r) (hδ : ripConst Xs (5 * r) < 1 / 10) (X0 : Matrix (Fin m) (Fin n) ℝ)
    (hX0 : X0.rank ≤ r) :
    ∀ X : Matrix (Fin m) (Fin n) ℝ, observationOp Xs X = observationOp Xs X0 →
      nuclearNorm X ≤ nuclearNorm X0 → X = X0 := by sorry

end MinRankRecovery.Recovery
