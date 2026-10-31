-- Prove2me | Theorems.Thm_LiqPremiaEq_eq_7_17_7_19
-- name    : LiqPremiaEq.eq_7_17_7_19
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:02:08.649258+00:00
-- url     : https://prove2.me/theorems/296a679b-7fb9-4b78-a6d8-42e7b2b0cbe4
-- title:
--   (7.17)–(7.19) — identities for $\Gamma$ and $c$ (corrected: index slip in (7.18))
-- statement:
--   Let $N\ge2$ and $\gamma^1,\dots,\gamma^N>0$, with $\bar\gamma$, $c$ and $\Gamma$ as in (3.4), Lemma 4.4 and (4.7). Then
--
--   $$\Gamma\Big(c+\frac{\bar\gamma}{\gamma^N}\mathbb 1_{N-1}\Big)=\frac{\gamma^N}N\mathbb 1_{N-1},\qquad(7.17)$$
--   $$(\Gamma^\top c)_n=\frac{\gamma^N-\gamma^n}N,\quad n=1,\dots,N-1,\qquad(7.18)$$
--   $$\mathbb 1_{N-1}^\top c=1-\bar\gamma\frac N{\gamma^N}.\qquad(7.19)$$
--
--   These identities turn the dynamics of the candidate rates into the price drift of Lemma 4.2 in the proof of Theorem 4.5.
--
--   Differences from the source:
--   - correction: (7.18): Γ⊤c = (1/N)[γᴺ − γⁿ ··· γᴺ − γ^{N−1}]⊤ (first entry printed with index n) → (Γ⊤c)ₙ = (γᴺ − γⁿ)/N for every n = 1, …, N − 1; reason: the first entry must be γᴺ − γ¹ (the last is γᴺ − γ^{N−1}); with dₙ = γⁿ − γᴺ, (Γ⊤c)ₙ = γ̄(1 − γⁿ/γᴺ) − (dₙ/N)(1 − Nγ̄/γᴺ) = (γᴺ − γⁿ)/N
--   - generalization: the standing assumption (3.2), γᴺ = max γⁿ → only γⁿ > 0; reason: the identities are algebraic and hold for all positive γ; the printed case is included
--   - encoding: agents n = 1, …, N with N ≥ 2; agent N the most risk-averse (3.2) → agents Fin (M + 1) with 1 ≤ M; agent N is Fin.last M; agents 1, …, N − 1 are Fin M via Fin.castSucc; reason: a relabelling of the same agents
--   - encoding: stacked vectors and matrices in ℝ^{K(N−1)}, ℝ^{K(N−1)×D}, ℝ^{(N−1)D×D}; Kronecker products A ⊗ B, c ⊗ I_K, c ⊗ Λ, 1_{N−1} ⊗ v → index types Fin M × Fin K (resp. Fin M × Fin D), block index first; Mathlib kroneckerMap; c ⊗ B as colKron c B (the Unit column index of a column vector dropped); 1 ⊗ v as onesKron v; reason: the same entries in the same block positions (p.3 convention)
-- source:
--   Muhle-Karbe–Shi–Yang, An Equilibrium Model for the Cross-Section of Liquidity Premia, arXiv:2011.13625v1, Proof of Theorem 4.5, eqs. (7.17)–(7.19), p.22

import Mathlib
import Definitions.Def_LiqPremiaEq_Gam

open Matrix

namespace LiqPremiaEq

/-- Identities (7.17)–(7.19) for the risk-aversion matrix `Γ` and the vector `c`:
`Γ (c + (γ̄/γᴺ) 1_{N−1}) = (γᴺ/N) 1_{N−1}`, `(Γᵀc)ₙ = (γᴺ − γⁿ)/N` for `n = 1, …, N − 1`, and
`1ᵀ_{N−1} c = 1 − γ̄N/γᴺ`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, Proof of Theorem 4.5, eqs. (7.17)–(7.19), p.22.

**Formalization Note** Corrected (7.18): the first entry is printed `γᴺ − γⁿ` and is
`γᴺ − γ¹`; the identity is stated componentwise. Only `γⁿ > 0` is assumed (not (3.2)). -/
theorem eq_7_17_7_19 {M : ℕ} (hM : 1 ≤ M) (γ : Fin (M + 1) → ℝ) (hγ : ∀ n, 0 < γ n) :
    Gam γ *ᵥ (cvec γ + (gbar γ / γ (Fin.last M)) • (fun _ => (1 : ℝ)))
        = (γ (Fin.last M) / ((M : ℝ) + 1)) • (fun _ => (1 : ℝ)) ∧
      (∀ n : Fin M, ((Gam γ)ᵀ *ᵥ cvec γ) n = (γ (Fin.last M) - γ n.castSucc) / ((M : ℝ) + 1)) ∧
      ∑ n, cvec γ n = 1 - gbar γ * ((M : ℝ) + 1) / γ (Fin.last M) := by sorry

end LiqPremiaEq
