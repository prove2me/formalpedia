-- Prove2me | Theorems.Thm_NetworkVolatility_Robust_theorem_4
-- name    : NetworkVolatility.Robust.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:47.908818+00:00
-- url     : https://prove2.me/theorems/07665b3b-dcd0-4bab-a1fd-95e9b46d6acf
-- title:
--   Theorem 4, p. 34 — $\rho(A)<1$ iff $A^k\to0$; then $(I-A)^{-1}=\sum_k A^k$; if $\rho(A)>1$ the powers are unbounded
-- statement:
--   Let $A$ be a real $n\times n$ matrix with spectral radius $\rho(A)$, the largest modulus of a (complex) eigenvalue of $A$. Then:
--
--   1. $\rho(A)<1$ if and only if $\lim_{k\to\infty}A^k=0$;
--   2. if $\rho(A)<1$, the matrix $I-A$ is invertible and its Neumann (Taylor) series converges:
--   $$(I-A)^{-1}=\sum_{k=0}^{\infty}A^k;$$
--   3. if $\rho(A)>1$, the powers $A^k$ are unbounded as $k$ grows.
--
--   This is the classical criterion (Horn and Johnson 1990, Theorem 5.6.12 and Corollary 5.6.16) the paper uses to show that $(I-\alpha W)^{-1}$ and $(I-\alpha\tilde W)^{-1}$ exist and are entrywise non-negative.
--
--   **Formalization Note** Limits and sums are entrywise (the product topology on matrices). Unboundedness in item 3 is stated entrywise: no constant bounds every $|(A^k)_{ij}|$, which is equivalent to $\|A^k\|$ being unbounded for any matrix norm.
-- source:
--   Baron, Hu & Malekian, Revenue volatility under uncertain network effects, SSRN preprint 3561270 (version of 2020-03-25), p. 34, Appendix A, Theorem 4

import Mathlib
import Definitions.Def_NetworkVolatility_Robust_Model

namespace NetworkVolatility.Robust

open Filter Topology

/-- Theorem 4 (Horn and Johnson 1990), p. 34, for a real `n × n` matrix `A` with spectral radius
`ρ(A)` (over `ℂ`): `ρ(A) < 1` iff `A^k → 0`; if `ρ(A) < 1`, `I - A` is invertible and
`(I - A)⁻¹ = Σ_{k ≥ 0} A^k`; if `ρ(A) > 1`, the powers `A^k` are unbounded. Convergence is
entrywise (the product topology on matrices). -/
theorem theorem_4 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (specRadius A < 1 ↔ Tendsto (fun k : ℕ => A ^ k) atTop (𝓝 0)) ∧
    (specRadius A < 1 → IsUnit (1 - A) ∧ HasSum (fun k : ℕ => A ^ k) (1 - A)⁻¹) ∧
    (1 < specRadius A → ¬ ∃ C : ℝ, ∀ (k : ℕ) (i j : Fin n), |(A ^ k) i j| ≤ C) := by sorry

end NetworkVolatility.Robust
