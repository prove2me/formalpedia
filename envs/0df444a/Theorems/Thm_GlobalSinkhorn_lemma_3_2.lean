-- Prove2me | Theorems.Thm_GlobalSinkhorn_lemma_3_2
-- name    : GlobalSinkhorn.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T04:23:14.952661+00:00
-- url     : https://prove2.me/theorems/15dc90f9-2f63-4583-b379-f1e2855c7c03
-- title:
--   Lemma 3.2 — one Sinkhorn–Knopp cycle contracts $\Phi$ by $1-(1-s_2(S)^4)/2$
-- statement:
--   Let $n\ge1$ and let $S$ be a nonnegative doubly stochastic $n\times n$ matrix with $s_2(S)<1$. Then for every $w\in\mathbb R^n_{>0}$,
--   $$
--   \Phi(\mathcal F(w))\le\Big(1-\frac{1-s_2(S)^4}{2}\Big)\,\Phi(w),
--   $$
--   where $\Phi(w)=\langle w^2\rangle\langle w^{-2}\rangle-1$ and $\mathcal F(w)=[S^\top(Sw)^{-1}]^{-1}$. Since one full column–row cycle of Sinkhorn–Knopp maps $M(w)$ to $M(\mathcal F(w))$, the potential of the iterates decays geometrically at a rate set by the spectral gap of the limit.
--
--   Differences from the source:
--   - encoding: indices [n] = {1,…,n} → Fin n (0-based); reason: Lean convention; same instances
--   - encoding: n a positive integer (p.13: n ∈ ℤ_{>0}) → hypothesis 0 < n; reason: the paper's standing convention made explicit
--   - encoding: s₂(S), second-largest singular value counted with multiplicity → (Matrix.toEuclideanLin S).singularValues 1 (0-indexed, with multiplicity); reason: Mathlib's singular values are nonincreasing and 0-indexed; index 1 is the second
--   - encoding: S nonnegative and doubly stochastic → S ∈ doublyStochastic ℝ (Fin n) (entries ≥ 0, all row and column sums 1); reason: Mathlib's doubly stochastic matrices are exactly the paper's
--   - encoding: M(w), F(w) defined with (Sw)⁻¹ and [Sᵀ(Sw)⁻¹]⁻¹ for w > 0 → Lean's total inverse in Mw, Fw; reason: for w > 0 and doubly stochastic S every inverted entry is positive (p.15), so the junk value 0 is never used
--   - encoding: ⟨v⟩ = (1/n) Σ_j v_j and componentwise powers/reciprocals → avg v = (Σ_j v j)/n, (w j)⁻¹, w j ^ 2; reason: notation of p.13 written out
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), Lemma 3.2, Eq. (24), p.15

import Mathlib
import Definitions.Def_GlobalSinkhorn_s2
import Definitions.Def_GlobalSinkhorn_potential
import Definitions.Def_GlobalSinkhorn_Fw

open Matrix

namespace GlobalSinkhorn

/-- Lemma 3.2: `Φ(F(w)) ≤ (1 − (1 − s₂(S)⁴)/2) Φ(w)`. He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), Lemma 3.2, Eq. (24), p.15. -/
theorem lemma_3_2 {n : ℕ} (hn : 0 < n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S ∈ doublyStochastic ℝ (Fin n)) (hs : s2 S < 1)
    (w : Fin n → ℝ) (hw : ∀ j, 0 < w j) :
    potential (Fw S w) ≤ (1 - (1 - s2 S ^ 4) / 2) * potential w := by sorry

end GlobalSinkhorn
