-- Prove2me | Theorems.Thm_MinRankRecovery_Recovery_ripConst_mono
-- name    : MinRankRecovery.Recovery.ripConst_mono
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T01:18:32.710414+00:00
-- url     : https://prove2.me/theorems/14667683-a0dc-404f-8567-019b2c09db0a
-- title:
--   §3, p. 12 — δ_r(𝒜) ≤ δ_r′(𝒜) for r ≤ r′
-- statement:
--   Let $\mathcal A:\mathbb R^{m\times n}\to\mathbb R^p$ be a linear map and $\delta_r(\mathcal A)$ its $r$-restricted isometry constant. For integers $r\le r'$,
--   $$\delta_r(\mathcal A)\le\delta_{r'}(\mathcal A).$$
--
--   Every matrix of rank at most $r$ also has rank at most $r'$, so the restricted isometry inequality at level $r'$ is the stronger requirement. The proof of Theorem 3.3 uses this in the form $\delta_{3r}\le\delta_{5r}$.
--
--   **Formalization Note** Stated for all natural numbers $r\le r'$, with $\delta_r$ as defined in this mission (`ripConst`, an infimum over $\delta\ge0$).
-- source:
--   Recht, Fazel & Parrilo, arXiv:0706.4138v1, §3, first sentence of p. 12

import Mathlib
import Definitions.Def_HighDimStat_MatrixRank_Core
import Definitions.Def_MinRankRecovery_Recovery_ripConst

open HighDimStat.MatrixRank Matrix

namespace MinRankRecovery.Recovery

/-- §3, p. 12: `δ_r(𝒜) ≤ δ_{r'}(𝒜)` for `r ≤ r'`. -/
theorem ripConst_mono {m n p : ℕ} (Xs : Fin p → Matrix (Fin m) (Fin n) ℝ) {r r' : ℕ}
    (h : r ≤ r') : ripConst Xs r ≤ ripConst Xs r' := by sorry

end MinRankRecovery.Recovery
