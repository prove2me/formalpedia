-- Prove2me | Theorems.Thm_GlobalSinkhorn_eq_31
-- name    : GlobalSinkhorn.eq_31
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T04:22:06.072966+00:00
-- url     : https://prove2.me/theorems/b56e0f32-8994-4ff0-9911-45e7be01141e
-- title:
--   Eq. (31) — $\langle w\rangle^2\langle w^{-1}\rangle^2\le(\langle w^2\rangle\langle w^{-2}\rangle+1)/2$
-- statement:
--   Let $n\ge1$ and $w\in\mathbb R^n_{>0}$. With $a=\langle w\rangle$, $b=\langle w^{-1}\rangle$, $p=\langle w^2\rangle$ and $q=\langle w^{-2}\rangle$ (componentwise powers, $\langle v\rangle=\frac1n\sum_jv_j$),
--   $$
--   a^2b^2\le\frac{pq+1}{2}.
--   $$
--   This scalar inequality closes the contraction estimate of Lemma 3.2.
--
--   Differences from the source:
--   - encoding: indices [n] = {1,…,n} → Fin n (0-based); reason: Lean convention; same instances
--   - encoding: n a positive integer (p.13: n ∈ ℤ_{>0}) → hypothesis 0 < n; reason: the paper's standing convention made explicit
--   - encoding: ⟨v⟩ = (1/n) Σ_j v_j and componentwise powers/reciprocals → avg v = (Σ_j v j)/n, (w j)⁻¹, w j ^ 2; reason: notation of p.13 written out
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), proof of Lemma 3.2, Eqs. (29)–(31), p.17

import Mathlib
import Definitions.Def_GlobalSinkhorn_avg

open Matrix

namespace GlobalSinkhorn

/-- Eq. (31): `a²b² ≤ (pq + 1)/2`, where `a = ⟨w⟩`, `b = ⟨w⁻¹⟩`, `p = ⟨w²⟩`, `q = ⟨w⁻²⟩`.
He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), proof of Lemma 3.2, Eqs. (29)–(31), p.17. -/
theorem eq_31 {n : ℕ} (hn : 0 < n) (w : Fin n → ℝ) (hw : ∀ j, 0 < w j) :
    avg w ^ 2 * avg (fun j => (w j)⁻¹) ^ 2 ≤
      (avg (fun j => w j ^ 2) * avg (fun j => (w j)⁻¹ ^ 2) + 1) / 2 := by sorry

end GlobalSinkhorn
