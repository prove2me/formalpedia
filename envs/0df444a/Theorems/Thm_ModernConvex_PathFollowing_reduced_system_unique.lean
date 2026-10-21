-- Prove2me | Theorems.Thm_ModernConvex_PathFollowing_reduced_system_unique
-- name    : ModernConvex.PathFollowing.reduced_system_unique
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:34:46.334835+00:00
-- url     : https://prove2.me/theorems/aec1c709-2dd4-4b66-a683-a87a9826acf5
-- title:
--   Proof of Theorem 6.5.2, step 3∗ — system (6.5.46) has a unique solution
-- statement:
--   Let $k \ge 1$, let $\mathcal L$ be a linear subspace of the space $\mathbf S^k$ of real symmetric $k\times k$ matrices, $\mathcal L^\perp$ its orthogonal complement in $\mathbf S^k$ for $\langle X, Y\rangle_F = \operatorname{Tr}(XY)$, and $B, C \in \mathbf S^k$. Let $0 < \chi \le \kappa \le 0.1$, and let $X = \operatorname{Diag}(x_1,\dots,x_k)$, $S = \operatorname{Diag}(s_1,\dots,s_k)$ with all $x_i, s_i > 0$, $X \in \mathcal L - B$, $S \in \mathcal L^\perp + C$,
--
--   $$\sum_{i=1}^k x_is_i = k, \qquad \sum_{i=1}^k (x_is_i - 1)^2 \le \kappa^2.$$
--
--   Put $\mu_+ = 1 - \chi k^{-1/2}$. Then the system in symmetric unknowns $\Delta X, \Delta S$
--
--   $$\Delta X \in \mathcal L,\qquad \Delta S \in \mathcal L^\perp,\qquad \Delta X\cdot S + X\cdot\Delta S + \Delta S\cdot X + S\cdot\Delta X = 2\mu_+I - 2XS \qquad (6.5.46)$$
--
--   has exactly one solution.
--
--   This is the normalized form ($\mu = \operatorname{Tr}(XS)/k = 1$, diagonal $X, S$, scaling $Q = I$) to which the proof of Theorem 6.5.2 reduces the well-definedness of the updating (U).
--
--   **Formalization Note** The hypotheses are the situation of step 2∗ after the normalization $\mu = 1$, (6.5.49)–(6.5.50) and (6.5.44), as on pp. 413–415; the book's (6.5.50) sums to $n$, a typo for $k$. The book's (6.5.46)(c) prints $X\Delta\cdot S$ for $X\cdot\Delta S$.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, pp. 413–416, proof of Theorem 6.5.2, step 3∗, system (6.5.46) under (6.5.44), (6.5.49), (6.5.50)

import Mathlib
import Definitions.Def_ModernConvex_PathFollowing_SDP

open Matrix
open scoped MatrixOrder

namespace ModernConvex.PathFollowing

/-- Ben-Tal–Nemirovski, proof of Theorem 6.5.2, step 3∗, p. 415: in the situation of step 2∗
(normalized to `μ = 1`: `X = Diag(x)`, `S = Diag(s)` positive definite, `X ∈ ℒ − B`,
`S ∈ ℒ⊥ + C`, (6.5.49), (6.5.50), (6.5.44)), the system (6.5.46) with `μ₊ = 1 − χk^{-1/2}`,
regarded as a system with symmetric unknowns `ΔX, ΔS`, has a unique solution. -/
theorem reduced_system_unique {k : ℕ} (hk : 0 < k) (P : SDPPair k) (κ χ : ℝ)
    (x s : Fin k → ℝ) (h : P.ReducedSituation κ χ x s) :
    ∃! d : Matrix (Fin k) (Fin k) ℝ × Matrix (Fin k) (Fin k) ℝ,
      P.IsReducedDirection (diagonal x) (diagonal s) (muPlus k χ) d.1 d.2 := by sorry

end ModernConvex.PathFollowing
