-- Prove2me | Theorems.Thm_MinRankRecovery_Recovery_theorem_3_2
-- name    : MinRankRecovery.Recovery.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:18:32.107078+00:00
-- url     : https://prove2.me/theorems/0bce62e5-c676-4552-a643-66364b83a69c
-- title:
--   Theorem 3.2 — if δ_2r < 1, X₀ is the only matrix of rank at most r with 𝒜(X) = 𝒜(X₀)
-- statement:
--   Let $\mathcal A:\mathbb R^{m\times n}\to\mathbb R^p$ be a linear map with restricted isometry constants $\delta_r=\delta_r(\mathcal A)$, let $r\ge1$ be an integer, and let $X_0\in\mathbb R^{m\times n}$ have rank at most $r$. Set $b=\mathcal A(X_0)$. If
--   $$\delta_{2r}<1,$$
--   then $X_0$ is the only matrix of rank at most $r$ satisfying $\mathcal A(X)=b$.
--
--   This is the uniqueness half of the theory: under the restricted isometry condition the linear measurements determine a low-rank matrix among all matrices of the same rank bound. It does not by itself give an efficient recovery procedure; Theorem 3.3 does.
--
--   **Formalization Note** The paper's section assumes $\operatorname{rank}X_0=r$; the statement here assumes $\operatorname{rank}X_0\le r$, a mild generalization: the paper's proof uses only that $X_0-X$ has rank at most $2r$, which holds whenever both matrices have rank at most $r$. The map is represented by measurement matrices as in Definition 3.1.
-- source:
--   Recht, Fazel & Parrilo, arXiv:0706.4138v1, Theorem 3.2, p. 12 (setting of (3.1), p. 11)

import Mathlib
import Definitions.Def_HighDimStat_MatrixRank_Core
import Definitions.Def_MinRankRecovery_Recovery_ripConst

open HighDimStat.MatrixRank Matrix

namespace MinRankRecovery.Recovery

/-- Theorem 3.2, p. 12: if `δ_2r < 1` for some `r ≥ 1`, then `X0` (of rank at most `r`) is the
only matrix of rank at most `r` with `𝒜(X) = 𝒜(X0)`. -/
theorem theorem_3_2 {m n p : ℕ} (Xs : Fin p → Matrix (Fin m) (Fin n) ℝ) (r : ℕ) (hr : 1 ≤ r)
    (hδ : ripConst Xs (2 * r) < 1) (X0 : Matrix (Fin m) (Fin n) ℝ) (hX0 : X0.rank ≤ r) :
    ∀ X : Matrix (Fin m) (Fin n) ℝ, X.rank ≤ r →
      observationOp Xs X = observationOp Xs X0 → X = X0 := by sorry

end MinRankRecovery.Recovery
