-- Prove2me | Theorems.Thm_ModernConvex_PathFollowing_scaled_direction_bounds
-- name    : ModernConvex.PathFollowing.scaled_direction_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:34:49.796014+00:00
-- url     : https://prove2.me/theorems/d40ff071-d373-4efa-b54f-dabe6f247388
-- title:
--   Eqs. (6.5.64)–(6.5.65) — Frobenius bounds on the scaled search directions
-- statement:
--   Work in the normalized situation of step 2∗ of the proof of Theorem 6.5.2: $k \ge 1$, $\mathcal L \subseteq \mathbf S^k$ a linear subspace with orthogonal complement $\mathcal L^\perp$ in $\mathbf S^k$, $B, C \in \mathbf S^k$, $0 < \chi \le \kappa \le 0.1$, $X = \operatorname{Diag}(x)$ and $S = \operatorname{Diag}(s)$ with $x_i, s_i > 0$, $X \in \mathcal L - B$, $S \in \mathcal L^\perp + C$, $\sum_i x_is_i = k$ and $\sum_i(x_is_i - 1)^2 \le \kappa^2$. Let $\mu_+ = 1 - \chi k^{-1/2}$ and let $(\Delta X, \Delta S)$ be a solution of (6.5.46): $\Delta X \in \mathcal L$, $\Delta S \in \mathcal L^\perp$, $\Delta X\cdot S + X\cdot\Delta S + \Delta S\cdot X + S\cdot\Delta X = 2\mu_+I - 2XS$. With $\delta X = X^{-1/2}\cdot\Delta X\cdot X^{-1/2}$ and $\delta S = X^{1/2}\cdot\Delta S\cdot X^{1/2}$ (6.5.51), the Frobenius norms satisfy
--
--   $$\|\delta X\|_2 \le \rho \equiv \frac{\sqrt{\chi^2+\kappa^2}}{1-\kappa}, \qquad \|\delta S\|_2 \le (1+\kappa)\rho.$$
--
--   These bounds drive the rest of the proof: they give positive definiteness of the updated pair and control the new distance to the central path.
--
--   **Formalization Note** $X^{1/2}$ is the positive semidefinite square root (`CFC.sqrt`) and $X^{-1/2}$ its inverse. The conclusion is stated for every solution of (6.5.46); uniqueness is a separate item.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, pp. 417–418, proof of Theorem 6.5.2, Eqs. (6.5.64)–(6.5.65), with (6.5.51)

import Mathlib
import Definitions.Def_ModernConvex_PathFollowing_SDP

open Matrix
open scoped MatrixOrder

namespace ModernConvex.PathFollowing

/-- Ben-Tal–Nemirovski, proof of Theorem 6.5.2, (6.5.64)–(6.5.65), pp. 417–418: in the situation
of step 2∗ (normalized to `μ = 1`), for the solution `(ΔX, ΔS)` of (6.5.46) with
`μ₊ = 1 − χk^{-1/2}`, the matrices `δX = X^{-1/2}·ΔX·X^{-1/2}` and `δS = X^{1/2}·ΔS·X^{1/2}`
of (6.5.51) satisfy `‖δX‖₂ ≤ ρ = √(χ² + κ²)/(1 − κ)` and `‖δS‖₂ ≤ (1 + κ)ρ`. -/
theorem scaled_direction_bounds {k : ℕ} (hk : 0 < k) (P : SDPPair k) (κ χ : ℝ)
    (x s : Fin k → ℝ) (h : P.ReducedSituation κ χ x s) (dX dS : Matrix (Fin k) (Fin k) ℝ)
    (hd : P.IsReducedDirection (diagonal x) (diagonal s) (muPlus k χ) dX dS) :
    frobNorm ((CFC.sqrt (diagonal x))⁻¹ * dX * (CFC.sqrt (diagonal x))⁻¹) ≤ rho κ χ ∧
      frobNorm (CFC.sqrt (diagonal x) * dS * CFC.sqrt (diagonal x)) ≤ (1 + κ) * rho κ χ := by sorry

end ModernConvex.PathFollowing
