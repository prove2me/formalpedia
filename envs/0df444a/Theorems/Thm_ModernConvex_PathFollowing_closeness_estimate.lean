-- Prove2me | Theorems.Thm_ModernConvex_PathFollowing_closeness_estimate
-- name    : ModernConvex.PathFollowing.closeness_estimate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:34:56.180379+00:00
-- url     : https://prove2.me/theorems/b8a4c3dc-1842-4605-8050-bfd906d25f08
-- title:
--   Eq. (6.5.73) — the distance of the updated pair to the central path
-- statement:
--   Work in the normalized situation of step 2∗ of the proof of Theorem 6.5.2: $k \ge 1$, $\mathcal L \subseteq \mathbf S^k$ a linear subspace with orthogonal complement $\mathcal L^\perp$ in $\mathbf S^k$, $B, C \in \mathbf S^k$, $0 < \chi \le \kappa \le 0.1$, $X = \operatorname{Diag}(x)$ and $S = \operatorname{Diag}(s)$ with $x_i, s_i > 0$, $X \in \mathcal L - B$, $S \in \mathcal L^\perp + C$, $\sum_i x_is_i = k$ and $\sum_i(x_is_i - 1)^2 \le \kappa^2$. Let $\mu_+ = 1 - \chi k^{-1/2}$, let $(\Delta X, \Delta S)$ solve (6.5.46): $\Delta X \in \mathcal L$, $\Delta S \in \mathcal L^\perp$, $\Delta X\cdot S + X\cdot\Delta S + \Delta S\cdot X + S\cdot\Delta X = 2\mu_+I - 2XS$, and let $X_+ = X + \Delta X$, $S_+ = S + \Delta S$. Then
--
--   $$\Omega \equiv \|\mu_+^{-1}X_+^{1/2}S_+X_+^{1/2} - I\|_2 \le \frac{\rho(1+\rho)}{1-\chi k^{-1/2}}\Big[\frac{\chi}{\sqrt k} + \frac{\rho}{1-\rho} + \frac{\kappa}{1-\kappa}\Big], \qquad \rho = \frac{\sqrt{\chi^2+\kappa^2}}{1-\kappa}.$$
--
--   $\Omega$ is the distance from $(X_+, S_+)$ to the point of the central path with penalty $t_+ = \mu_+^{-1}$, so this estimate is what keeps the iterate in $\mathcal N_\kappa$.
--
--   **Formalization Note** $X_+^{1/2}$ is the positive semidefinite square root (`CFC.sqrt`); the bound is stated for every solution of (6.5.46). The book's intermediate quantity $\widehat\Omega$ is not part of the statement.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 421, proof of Theorem 6.5.2, Eq. (6.5.73) (with (6.5.48))

import Mathlib
import Definitions.Def_ModernConvex_PathFollowing_SDP

open Matrix
open scoped MatrixOrder

namespace ModernConvex.PathFollowing

/-- Ben-Tal–Nemirovski, proof of Theorem 6.5.2, (6.5.73), p. 421: in the situation of step 2∗
(normalized to `μ = 1`), for the solution `(ΔX, ΔS)` of (6.5.46) with `μ₊ = 1 − χk^{-1/2}` and
`X₊ = X + ΔX`, `S₊ = S + ΔS`,
`Ω = ‖μ₊⁻¹X₊^{1/2}S₊X₊^{1/2} − I‖₂ ≤ ρ(1+ρ)/(1 − χk^{-1/2}) · (χ/√k + ρ/(1−ρ) + κ/(1−κ))`,
`ρ = √(χ² + κ²)/(1 − κ)`. -/
theorem closeness_estimate {k : ℕ} (hk : 0 < k) (P : SDPPair k) (κ χ : ℝ)
    (x s : Fin k → ℝ) (h : P.ReducedSituation κ χ x s) (dX dS : Matrix (Fin k) (Fin k) ℝ)
    (hd : P.IsReducedDirection (diagonal x) (diagonal s) (muPlus k χ) dX dS) :
    centralPathDist (muPlus k χ)⁻¹ (diagonal x + dX) (diagonal s + dS) ≤
      closenessBound k κ χ := by sorry

end ModernConvex.PathFollowing
