-- Prove2me | Theorems.Thm_GlobalSinkhorn_F_le_P
-- name    : GlobalSinkhorn.F_le_P
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T04:22:19.713009+00:00
-- url     : https://prove2.me/theorems/ff88a931-c4d9-4a73-aa61-a5fbd03f3a14
-- title:
--   Eqs. (27)–(28) — $0<\mathcal F(w)\le Pw$ and $\mathcal F(w)^{-1}\le P(w^{-1})$
-- statement:
--   Let $n\ge1$, let $S$ be a nonnegative doubly stochastic $n\times n$ matrix, put $P=S^\top S$, and let $w\in\mathbb R^n_{>0}$. Then
--   1. $(Sw)_i>0$ for every $i$;
--   2. $\mathcal F(w)_j>0$ for every $j$;
--   3. $\mathcal F(w)\le Pw$ componentwise;
--   4. $\mathcal F(w)^{-1}\le P(w^{-1})$ componentwise,
--
--   where $\mathcal F(w)=[S^\top(Sw)^{-1}]^{-1}$ and reciprocals are componentwise. Items 1–2 make $M(w)$ and $\mathcal F(w)$ well defined; items 3–4 (Cauchy–Schwarz and Jensen) reduce the potential of $\mathcal F(w)$ to second moments of $Pw$ and $P(w^{-1})$.
--
--   Differences from the source:
--   - encoding: indices [n] = {1,…,n} → Fin n (0-based); reason: Lean convention; same instances
--   - encoding: n a positive integer (p.13: n ∈ ℤ_{>0}) → hypothesis 0 < n; reason: the paper's standing convention made explicit
--   - encoding: S nonnegative and doubly stochastic → S ∈ doublyStochastic ℝ (Fin n) (entries ≥ 0, all row and column sums 1); reason: Mathlib's doubly stochastic matrices are exactly the paper's
--   - encoding: M(w), F(w) defined with (Sw)⁻¹ and [Sᵀ(Sw)⁻¹]⁻¹ for w > 0 → Lean's total inverse in Mw, Fw; reason: for w > 0 and doubly stochastic S every inverted entry is positive (p.15), so the junk value 0 is never used
--   - encoding: vector inequalities "componentwise" → ∀ j, …; reason: written out
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), p.15 after Eq. (22), and proof of Lemma 3.2, Eqs. (27)–(28), pp.16–17

import Mathlib
import Definitions.Def_GlobalSinkhorn_Fw

open Matrix

namespace GlobalSinkhorn

/-- `S w > 0`, `F(w) > 0`, `F(w) ≤ P w` and `F(w)⁻¹ ≤ P(w⁻¹)` componentwise, with `P = SᵀS`.
He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), p.15 after Eq. (22) and proof of Lemma 3.2, Eqs. (27)–(28), pp.16–17. -/
theorem F_le_P {n : ℕ} (hn : 0 < n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S ∈ doublyStochastic ℝ (Fin n)) (w : Fin n → ℝ) (hw : ∀ j, 0 < w j) :
    (∀ i, 0 < (S *ᵥ w) i) ∧ (∀ j, 0 < Fw S w j) ∧
      (∀ j, Fw S w j ≤ ((Sᵀ * S) *ᵥ w) j) ∧
      ∀ j, (Fw S w j)⁻¹ ≤ ((Sᵀ * S) *ᵥ (fun k => (w k)⁻¹)) j := by sorry

end GlobalSinkhorn
