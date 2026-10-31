-- Prove2me | Theorems.Thm_LiqPremiaEq_corollary_7_7
-- name    : LiqPremiaEq.corollary_7_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:03:00.761306+00:00
-- url     : https://prove2.me/theorems/19edd937-5e69-451a-b1a2-f9e374158436
-- title:
--   Corollary 7.7 — the Riccati solution $F$ stays positive semidefinite
-- statement:
--   Let $N\ge2$, $\gamma^n>0$ with $\gamma^N$ maximal, $\Lambda$ symmetric positive definite, and $\alpha$, $\xi$ arbitrary. If $(F,H)$ solves the matrix Riccati system (4.8) on an initial interval $[0,T')$, then $F(\tau)$ is positive semidefinite ($b^\top F(\tau)b\ge0$, no symmetry) for every $\tau\in[0,T')$.
--
--   The paper states this for the unique local solution on its maximal interval of existence $[0,T_{\max})$. Positive semidefiniteness of $F$ is what makes $\Psi_F$ a contraction (Corollary 7.8) and so excludes blow-up of (4.8).
--
--   Differences from the source:
--   - generalization: the unique local solution (F, H) of (4.8) on its maximal interval [0, T_max) → any solution on any initial interval [0, T′), T′ ∈ ℝ; reason: the proof never uses maximality or the whole half-line; taking T′ = T_max (resp. every T′ = τ + 1) gives the printed statement
--   - reading: positive (semi)definite → IsPSDQuad A: bᵀAb ≥ 0 for all b (IsPDQuad: bᵀAb > 0 for b ≠ 0), no symmetry required; reason: footnotes 10 (p.8) and 19 (p.14): the matrices are not symmetric and the notions are meant without symmetry
--   - encoding: agents n = 1, …, N with N ≥ 2; agent N the most risk-averse (3.2) → agents Fin (M + 1) with 1 ≤ M; agent N is Fin.last M; agents 1, …, N − 1 are Fin M via Fin.castSucc; reason: a relabelling of the same agents
--   - encoding: stacked vectors and matrices in ℝ^{K(N−1)}, ℝ^{K(N−1)×D}, ℝ^{(N−1)D×D}; Kronecker products A ⊗ B, c ⊗ I_K, c ⊗ Λ, 1_{N−1} ⊗ v → index types Fin M × Fin K (resp. Fin M × Fin D), block index first; Mathlib kroneckerMap; c ⊗ B as colKron c B (the Unit column index of a column vector dropped); 1 ⊗ v as onesKron v; reason: the same entries in the same block positions (p.3 convention)
--   - encoding: matrix ODEs on an interval → every entry has the stated derivative within the interval at each of its points (one-sided at the endpoints); reason: entrywise differentiability is differentiability of a matrix function on a finite-dimensional space
-- source:
--   Muhle-Karbe–Shi–Yang, An Equilibrium Model for the Cross-Section of Liquidity Premia, arXiv:2011.13625v1, Corollary 7.7, pp.18–19

import Mathlib
import Definitions.Def_LiqPremiaEq_IsPSDQuad
import Definitions.Def_LiqPremiaEq_IsRiccatiSolOn

open Matrix

namespace LiqPremiaEq

/-- **Corollary 7.7.** Let `(F, H)` solve the matrix Riccati system (4.8) on an initial interval
`[0, T′)`. Then `F(τ)` is positive semidefinite for every `τ ∈ [0, T′)`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, Corollary 7.7, pp.18–19.

**Formalization Note** The paper takes the unique local solution on its maximal interval
`[0, T_max)`; here any solution on any initial interval `[0, T′)` (in particular the maximal one).
`N = M + 1 ≥ 2` agents with `γⁿ > 0` and (3.2); `Λ` symmetric positive definite; `α`, `ξ`
arbitrary. Positive semidefinite means `bᵀFb ≥ 0` without symmetry. -/
theorem corollary_7_7 {M K D : ℕ} (hM : 1 ≤ M) (γ : Fin (M + 1) → ℝ) (hγ : ∀ n, 0 < γ n)
    (hγN : ∀ n, γ n ≤ γ (Fin.last M)) (Λ : Matrix (Fin K) (Fin K) ℝ) (hΛ : Λ.PosDef)
    (α : Matrix (Fin K) (Fin D) ℝ) (ξ : Fin M → Matrix (Fin D) (Fin D) ℝ) (T' : ℝ)
    (F : ℝ → Matrix (Fin M × Fin K) (Fin M × Fin K) ℝ) (H : ℝ → Matrix (Fin M × Fin K) (Fin D) ℝ)
    (hFH : IsRiccatiSolOn γ Λ α ξ (Set.Ico 0 T') F H) :
    ∀ τ ∈ Set.Ico 0 T', IsPSDQuad (F τ) := by sorry

end LiqPremiaEq
