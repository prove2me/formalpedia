-- Prove2me | Theorems.Thm_GlobalSinkhorn_eq_25
-- name    : GlobalSinkhorn.eq_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T04:22:20.261205+00:00
-- url     : https://prove2.me/theorems/6979f5c4-ca14-4ef2-9215-8ecd708b8f09
-- title:
--   Eq. (25) — $\|Pz\|_2^2\le s_2(S)^4\|z\|_2^2$ for $z\perp\mathbf 1$
-- statement:
--   Let $n\ge1$ and let $S$ be a nonnegative doubly stochastic $n\times n$ matrix with $s_2(S)<1$. Put $P=S^\top S$ and $\theta=s_2(S)^4$. Then for every $z\in\mathbb R^n$ with $z\perp\mathbf 1$, i.e. $\sum_iz_i=0$,
--   $$
--   \|Pz\|_2^2\le\theta\,\|z\|_2^2 .
--   $$
--   This is the spectral input to Lemma 3.2: $P$ is symmetric positive semidefinite with $P\mathbf 1=\mathbf 1$, and on $\mathbf 1^\perp$ its norm is $s_2(S)^2$.
--
--   Differences from the source:
--   - encoding: indices [n] = {1,…,n} → Fin n (0-based); reason: Lean convention; same instances
--   - encoding: n a positive integer (p.13: n ∈ ℤ_{>0}) → hypothesis 0 < n; reason: the paper's standing convention made explicit
--   - encoding: s₂(S), second-largest singular value counted with multiplicity → (Matrix.toEuclideanLin S).singularValues 1 (0-indexed, with multiplicity); reason: Mathlib's singular values are nonincreasing and 0-indexed; index 1 is the second
--   - encoding: S nonnegative and doubly stochastic → S ∈ doublyStochastic ℝ (Fin n) (entries ≥ 0, all row and column sums 1); reason: Mathlib's doubly stochastic matrices are exactly the paper's
--   - encoding: z ⊥ 1, ‖·‖₂² → Σ i, z i = 0, sums of squares; reason: standard inner product on ℝⁿ written out
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), proof of Lemma 3.2, Eq. (25), p.15

import Mathlib
import Definitions.Def_GlobalSinkhorn_s2

open Matrix

namespace GlobalSinkhorn

/-- Eq. (25): `‖P z‖₂² ≤ θ ‖z‖₂²` whenever `z ⊥ 1`, with `P = SᵀS`, `θ = s₂(S)⁴`.
He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), proof of Lemma 3.2, Eq. (25), p.15.

**Formalization Note.** Squared `ℓ₂` norms are written as sums of squares, and `z ⊥ 1` as
`∑ i, z i = 0`. -/
theorem eq_25 {n : ℕ} (hn : 0 < n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S ∈ doublyStochastic ℝ (Fin n)) (hs : s2 S < 1)
    (z : Fin n → ℝ) (hz : ∑ i, z i = 0) :
    ∑ i, ((Sᵀ * S) *ᵥ z) i ^ 2 ≤ s2 S ^ 4 * ∑ i, z i ^ 2 := by sorry

end GlobalSinkhorn
