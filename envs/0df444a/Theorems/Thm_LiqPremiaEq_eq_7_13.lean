-- Prove2me | Theorems.Thm_LiqPremiaEq_eq_7_13
-- name    : LiqPremiaEq.eq_7_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:03:03.646519+00:00
-- url     : https://prove2.me/theorems/bfb725c4-f309-46da-9edd-f236ce48cd27
-- title:
--   (7.13) — $\|\alpha+(c\otimes I_K)^\top H(\tau)\|_{op}\le\|\alpha\|\exp(\|c\|\|\Lambda\|^{1/2}\|\Lambda^{-1}\|^{1/2}\|\Gamma\|\|\xi\|\tau)$
-- statement:
--   Let $N\ge2$, $\gamma^n>0$ with $\gamma^N$ maximal, $\Lambda$ symmetric positive definite, $\alpha\in\mathbb R^{K\times D}$ and $\xi\in\mathbb R^{(N-1)D\times D}$. If $(F,H)$ solves the Riccati system (4.8) on $[0,T')$, then for every $\tau\in[0,T')$
--
--   $$\big\|\alpha+(c\otimes I_K)^\top H(\tau)\big\|_{op}\le\|\alpha\|\exp\big(\|c\|\,\|\Lambda\|^{1/2}\|\Lambda^{-1}\|^{1/2}\|\Gamma\|\,\|\xi\|\,\tau\big),$$
--
--   where $\|\cdot\|_{op}$ is the operator norm and all norms on the right are Frobenius norms.
--
--   The left side is the operator norm of the endogenous equilibrium volatility $\sigma_t=\alpha+(c\otimes I_K)^\top H(T-t)$ of (7.20); the bound implies that $H$, and then $F$, stay bounded on finite intervals.
--
--   Differences from the source:
--   - generalization: τ ∈ [0, T_max), the maximal interval of the local solution of (4.8) → any solution on any initial interval [0, T′), T′ ∈ ℝ; reason: the proof never uses maximality or the whole half-line; taking T′ = T_max (resp. every T′ = τ + 1) gives the printed statement
--   - encoding: agents n = 1, …, N with N ≥ 2; agent N the most risk-averse (3.2) → agents Fin (M + 1) with 1 ≤ M; agent N is Fin.last M; agents 1, …, N − 1 are Fin M via Fin.castSucc; reason: a relabelling of the same agents
--   - encoding: stacked vectors and matrices in ℝ^{K(N−1)}, ℝ^{K(N−1)×D}, ℝ^{(N−1)D×D}; Kronecker products A ⊗ B, c ⊗ I_K, c ⊗ Λ, 1_{N−1} ⊗ v → index types Fin M × Fin K (resp. Fin M × Fin D), block index first; Mathlib kroneckerMap; c ⊗ B as colKron c B (the Unit column index of a column vector dropped); 1 ⊗ v as onesKron v; reason: the same entries in the same block positions (p.3 convention)
--   - encoding: matrix ODEs on an interval → every entry has the stated derivative within the interval at each of its points (one-sided at the endpoints); reason: entrywise differentiability is differentiability of a matrix function on a finite-dimensional space
--   - encoding: Frobenius norm ‖·‖ (p.3) and operator norm ‖·‖op (Definition 7.2) → explicit functions frobVec, frob and opNorm (the ℓ² operator norm of Matrix.toEuclideanLin A); reason: avoids Mathlib’s default sup norm; same values
-- source:
--   Muhle-Karbe–Shi–Yang, An Equilibrium Model for the Cross-Section of Liquidity Premia, arXiv:2011.13625v1, Proof of Lemma 4.4, eq. (7.13), p.20

import Mathlib
import Definitions.Def_LiqPremiaEq_opNorm
import Definitions.Def_LiqPremiaEq_IsRiccatiSolOn

open Matrix

namespace LiqPremiaEq

/-- **(7.13)**, the Gronwall bound on the endogenous volatility: for a solution `(F, H)` of the
Riccati system (4.8) on `[0, T′)`,
`‖α + (c ⊗ I_K)ᵀH(τ)‖op ≤ ‖α‖ exp(‖c‖ ‖Λ‖^{1/2} ‖Λ⁻¹‖^{1/2} ‖Γ‖ ‖ξ‖ τ)` for `τ ∈ [0, T′)`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, Proof of Lemma 4.4, eq. (7.13), p.20.

**Formalization Note** The left side is the `ℓ²` operator norm; `‖α‖`, `‖c‖`, `‖Λ‖`, `‖Λ⁻¹‖`,
`‖Γ‖` and `‖ξ‖` are Frobenius norms (Notation, p.3), `ξ ∈ ℝ^{(N−1)D×D}` the stacked matrix of
Assumption 4.3. The paper's `[0, T_max)` is replaced by any initial interval `[0, T′)` on which
`(F, H)` solves (4.8). -/
theorem eq_7_13 {M K D : ℕ} (hM : 1 ≤ M) (γ : Fin (M + 1) → ℝ) (hγ : ∀ n, 0 < γ n)
    (hγN : ∀ n, γ n ≤ γ (Fin.last M)) (Λ : Matrix (Fin K) (Fin K) ℝ) (hΛ : Λ.PosDef)
    (α : Matrix (Fin K) (Fin D) ℝ) (ξ : Fin M → Matrix (Fin D) (Fin D) ℝ) (T' : ℝ)
    (F : ℝ → Matrix (Fin M × Fin K) (Fin M × Fin K) ℝ) (H : ℝ → Matrix (Fin M × Fin K) (Fin D) ℝ)
    (hFH : IsRiccatiSolOn γ Λ α ξ (Set.Ico 0 T') F H) :
    ∀ τ ∈ Set.Ico 0 T', opNorm (sigmaH γ α (H τ)) ≤
      frob α * Real.exp (frobVec (cvec γ) * Real.sqrt (frob Λ) * Real.sqrt (frob Λ⁻¹)
        * frob (Gam γ) * frob (stackMat ξ) * τ) := by sorry

end LiqPremiaEq
