-- Prove2me | Theorems.Thm_ModernConvex_PathFollowing_closeness_bound_le_kappa
-- name    : ModernConvex.PathFollowing.closeness_bound_le_kappa
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:35:04.585337+00:00
-- url     : https://prove2.me/theorems/5d18b8b9-690f-425f-b7e2-82de4b19e440
-- title:
--   p. 421 after (6.5.73) — for 0 < χ ≤ κ ≤ 0.1 the closeness bound is at most κ
-- statement:
--   Let $k \ge 1$ be an integer and $0 < \chi \le \kappa \le 0.1$. Put $\rho = \sqrt{\chi^2+\kappa^2}/(1-\kappa)$. Then
--
--   $$\frac{\rho(1+\rho)}{1-\chi k^{-1/2}}\Big[\frac{\chi}{\sqrt k} + \frac{\rho}{1-\rho} + \frac{\kappa}{1-\kappa}\Big] \le \kappa.$$
--
--   This is the numerical fact that closes the proof of Theorem 6.5.2: the right-hand side of (6.5.73) is at most $\kappa$, so one step of the updating (U) keeps the iterate in the neighbourhood $\mathcal N_\kappa$ of the central path.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 421, the sentence after (6.5.73) in the proof of Theorem 6.5.2

import Mathlib
import Definitions.Def_ModernConvex_PathFollowing_SDP

open Matrix
open scoped MatrixOrder

namespace ModernConvex.PathFollowing

/-- Ben-Tal–Nemirovski, p. 421, after (6.5.73): if `0 < χ ≤ κ ≤ 0.1`, the right-hand side of
(6.5.73), `ρ(1+ρ)/(1 − χk^{-1/2}) · (χ/√k + ρ/(1−ρ) + κ/(1−κ))` with
`ρ = √(χ² + κ²)/(1 − κ)`, is at most `κ`, for every `k ≥ 1`. -/
theorem closeness_bound_le_kappa (k : ℕ) (hk : 0 < k) (κ χ : ℝ) (hχ : 0 < χ) (hχκ : χ ≤ κ)
    (hκ : κ ≤ 0.1) :
    closenessBound k κ χ ≤ κ := by sorry

end ModernConvex.PathFollowing
