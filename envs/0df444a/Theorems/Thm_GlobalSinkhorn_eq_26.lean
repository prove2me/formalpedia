-- Prove2me | Theorems.Thm_GlobalSinkhorn_eq_26
-- name    : GlobalSinkhorn.eq_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T04:22:33.720201+00:00
-- url     : https://prove2.me/theorems/d0e8722f-67aa-4334-80f1-ebf21ed3ad2e
-- title:
--   Eq. (26) — $\langle (Pz)^2\rangle\le\theta\langle z^2\rangle+(1-\theta)\langle z\rangle^2$
-- statement:
--   Let $n\ge1$ and let $S$ be a nonnegative doubly stochastic $n\times n$ matrix with $s_2(S)<1$. Put $P=S^\top S$ and $\theta=s_2(S)^4$. Then for every $z\in\mathbb R^n$,
--   $$
--   \big\langle (Pz)^2\big\rangle\le\theta\,\langle z^2\rangle+(1-\theta)\,\langle z\rangle^2,
--   $$
--   where squares are componentwise and $\langle v\rangle=\frac1n\sum_jv_j$. Applied to $z=w$ and $z=w^{-1}$, it bounds the second moments of $\mathcal F(w)$ and $\mathcal F(w)^{-1}$ in the proof of Lemma 3.2.
--
--   Differences from the source:
--   - encoding: indices [n] = {1,…,n} → Fin n (0-based); reason: Lean convention; same instances
--   - encoding: n a positive integer (p.13: n ∈ ℤ_{>0}) → hypothesis 0 < n; reason: the paper's standing convention made explicit
--   - encoding: s₂(S), second-largest singular value counted with multiplicity → (Matrix.toEuclideanLin S).singularValues 1 (0-indexed, with multiplicity); reason: Mathlib's singular values are nonincreasing and 0-indexed; index 1 is the second
--   - encoding: S nonnegative and doubly stochastic → S ∈ doublyStochastic ℝ (Fin n) (entries ≥ 0, all row and column sums 1); reason: Mathlib's doubly stochastic matrices are exactly the paper's
--   - encoding: ⟨v⟩ = (1/n) Σ_j v_j and componentwise powers/reciprocals → avg v = (Σ_j v j)/n, (w j)⁻¹, w j ^ 2; reason: notation of p.13 written out
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), proof of Lemma 3.2, Eq. (26), p.16

import Mathlib
import Definitions.Def_GlobalSinkhorn_s2
import Definitions.Def_GlobalSinkhorn_avg

open Matrix

namespace GlobalSinkhorn

/-- Eq. (26): `⟨(P z)²⟩ ≤ θ ⟨z²⟩ + (1 − θ) ⟨z⟩²` for every `z`, with `P = SᵀS`, `θ = s₂(S)⁴`.
He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), proof of Lemma 3.2, Eq. (26), p.16. -/
theorem eq_26 {n : ℕ} (hn : 0 < n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S ∈ doublyStochastic ℝ (Fin n)) (hs : s2 S < 1) (z : Fin n → ℝ) :
    avg (fun i => ((Sᵀ * S) *ᵥ z) i ^ 2) ≤
      s2 S ^ 4 * avg (fun i => z i ^ 2) + (1 - s2 S ^ 4) * avg z ^ 2 := by sorry

end GlobalSinkhorn
