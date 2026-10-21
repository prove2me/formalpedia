-- Prove2me | Theorems.Thm_ModernConvex_PathFollowing_updated_pair_feasible
-- name    : ModernConvex.PathFollowing.updated_pair_feasible
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:34:52.260999+00:00
-- url     : https://prove2.me/theorems/ccb6ea50-11c8-4147-9948-8544c6a1c53a
-- title:
--   Proof of Theorem 6.5.2, 2∗(i)–(ii), (6.5.47), (6.5.66) — the updated pair is strictly feasible
-- statement:
--   Work in the normalized situation of step 2∗ of the proof of Theorem 6.5.2: $k \ge 1$, $\mathcal L \subseteq \mathbf S^k$ a linear subspace with orthogonal complement $\mathcal L^\perp$ in $\mathbf S^k$, $B, C \in \mathbf S^k$, $0 < \chi \le \kappa \le 0.1$, $X = \operatorname{Diag}(x)$ and $S = \operatorname{Diag}(s)$ with $x_i, s_i > 0$, $X \in \mathcal L - B$, $S \in \mathcal L^\perp + C$, $\sum_i x_is_i = k$ and $\sum_i(x_is_i - 1)^2 \le \kappa^2$. Let $\mu_+ = 1 - \chi k^{-1/2}$, $\rho = \sqrt{\chi^2+\kappa^2}/(1-\kappa)$, and let $(\Delta X, \Delta S)$ solve (6.5.46): $\Delta X \in \mathcal L$, $\Delta S \in \mathcal L^\perp$, $\Delta X\cdot S + X\cdot\Delta S + \Delta S\cdot X + S\cdot\Delta X = 2\mu_+I - 2XS$. Then $X_+ = X + \Delta X$ and $S_+ = S + \Delta S$ satisfy:
--
--   1. $X_+ \succ 0$ and $S_+ \succ 0$;
--   2. $X_+ \in \mathcal L - B$ and $S_+ \in \mathcal L^\perp + C$;
--   3. $\operatorname{Tr}(X_+S_+) = \mu_+k$ (6.5.47);
--   4. $X_+ \preceq (1+\rho)X$ (6.5.66).
--
--   **Formalization Note** $\preceq$ is the Löwner order: $(1+\rho)X - X_+$ is positive semidefinite.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 414 (2∗(i)–(ii), (6.5.47)) and p. 418 (step 5∗, (6.5.66)), proof of Theorem 6.5.2

import Mathlib
import Definitions.Def_ModernConvex_PathFollowing_SDP

open Matrix
open scoped MatrixOrder

namespace ModernConvex.PathFollowing

/-- Ben-Tal–Nemirovski, proof of Theorem 6.5.2, 2∗(i)–(ii) with (6.5.47) and (6.5.66),
pp. 414, 418: in the situation of step 2∗ (normalized to `μ = 1`), for the solution `(ΔX, ΔS)`
of (6.5.46) with `μ₊ = 1 − χk^{-1/2}`, the matrices `X₊ = X + ΔX`, `S₊ = S + ΔS` are positive
definite, belong to `ℒ − B`, `ℒ⊥ + C` respectively, satisfy `Tr(X₊S₊) = μ₊k`, and
`X₊ ⪯ (1 + ρ)X` with `ρ = √(χ² + κ²)/(1 − κ)`. -/
theorem updated_pair_feasible {k : ℕ} (hk : 0 < k) (P : SDPPair k) (κ χ : ℝ)
    (x s : Fin k → ℝ) (h : P.ReducedSituation κ χ x s) (dX dS : Matrix (Fin k) (Fin k) ℝ)
    (hd : P.IsReducedDirection (diagonal x) (diagonal s) (muPlus k χ) dX dS) :
    (diagonal x + dX).PosDef ∧ (diagonal s + dS).PosDef ∧
      diagonal x + dX + P.B ∈ P.L ∧ diagonal s + dS - P.C ∈ orthSym P.L ∧
      ((diagonal x + dX) * (diagonal s + dS)).trace = muPlus k χ * k ∧
      ((1 + rho κ χ) • diagonal x - (diagonal x + dX)).PosSemidef := by sorry

end ModernConvex.PathFollowing
