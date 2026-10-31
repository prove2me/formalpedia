-- Prove2me | Theorems.Thm_LiqPremiaEq_corollary_7_8
-- name    : LiqPremiaEq.corollary_7_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:03:18.735335+00:00
-- url     : https://prove2.me/theorems/df02fe24-a690-478a-97f7-2dddf89f30b3
-- title:
--   Corollary 7.8 — $\|\Psi_F(r;\tau)\|_{op}\le1$ for $0\le r\le\tau$
-- statement:
--   Let $(F,H)$ solve (4.8) on $[0,T')$ and let $\Phi_F$ solve the linear matrix ODE
--
--   $$\Phi_F'(\tau)=(I_{N-1}\otimes\Lambda^{-1/2})F^\top(\tau)(I_{N-1}\otimes\Lambda^{-1/2})\Phi_F(\tau),\qquad\Phi_F(0)=I_{K(N-1)}\qquad(7.7)$$
--
--   on $[0,T')$. Then $\Phi_F(\tau)$ is invertible for $\tau\in[0,T')$, and
--
--   $$\Psi_F(r;\tau)=\Phi_F(r)\Phi_F^{-1}(\tau)\qquad(7.9)$$
--
--   satisfies $\|\Psi_F(r;\tau)\|_{op}\le1$ for every $0\le r\le\tau<T'$.
--
--   The bound is the a-priori estimate that, through the variation-of-constants formulas (7.11)–(7.12) and Gronwall's inequality, rules out blow-up of the Riccati system.
--
--   Differences from the source:
--   - generalization: Φ_F and Ψ_F on the maximal interval [0, T_max) of the local solution of (4.8) → any solution on any initial interval [0, T′), T′ ∈ ℝ; reason: the proof never uses maximality or the whole half-line; taking T′ = T_max (resp. every T′ = τ + 1) gives the printed statement
--   - reading: (7.9) defines Ψ_F with Φ_F⁻¹(τ); invertibility of Φ_F(τ) is shown by Liouville’s formula on p.20 → the conclusion also asserts IsUnit (Φ_F τ).det for τ ∈ [0, T′); reason: the definition (7.9) presupposes invertibility; Lean’s matrix inverse is total, so it is stated
--   - encoding: Λ^{1/2}, the unique symmetric positive definite square root of Λ (footnote 5), and Λ^{−1/2} → a parameter R with Rᵀ = R, R positive definite and R * R = Λ; Λ^{−1/2} is R⁻¹; reason: the hypotheses determine R uniquely, so R is Λ^{1/2}
--   - encoding: agents n = 1, …, N with N ≥ 2; agent N the most risk-averse (3.2) → agents Fin (M + 1) with 1 ≤ M; agent N is Fin.last M; agents 1, …, N − 1 are Fin M via Fin.castSucc; reason: a relabelling of the same agents
--   - encoding: stacked vectors and matrices in ℝ^{K(N−1)}, ℝ^{K(N−1)×D}, ℝ^{(N−1)D×D}; Kronecker products A ⊗ B, c ⊗ I_K, c ⊗ Λ, 1_{N−1} ⊗ v → index types Fin M × Fin K (resp. Fin M × Fin D), block index first; Mathlib kroneckerMap; c ⊗ B as colKron c B (the Unit column index of a column vector dropped); 1 ⊗ v as onesKron v; reason: the same entries in the same block positions (p.3 convention)
--   - encoding: matrix ODEs on an interval → every entry has the stated derivative within the interval at each of its points (one-sided at the endpoints); reason: entrywise differentiability is differentiability of a matrix function on a finite-dimensional space
--   - encoding: Frobenius norm ‖·‖ (p.3) and operator norm ‖·‖op (Definition 7.2) → explicit functions frobVec, frob and opNorm (the ℓ² operator norm of Matrix.toEuclideanLin A); reason: avoids Mathlib’s default sup norm; same values
-- source:
--   Muhle-Karbe–Shi–Yang, An Equilibrium Model for the Cross-Section of Liquidity Premia, arXiv:2011.13625v1, Corollary 7.8 and eqs. (7.7), (7.9), pp.18–19; invertibility of Φ_F, p.20

import Mathlib
import Definitions.Def_LiqPremiaEq_opNorm
import Definitions.Def_LiqPremiaEq_IsRiccatiSolOn
import Definitions.Def_LiqPremiaEq_phiCoeff

open Matrix

namespace LiqPremiaEq

/-- **Corollary 7.8.** Let `(F, H)` solve (4.8) on `[0, T′)` and let `Φ_F` solve the linear matrix
ODE (7.7), `Φ_F′(τ) = (I_{N−1} ⊗ Λ^{−1/2}) Fᵀ(τ) (I_{N−1} ⊗ Λ^{−1/2}) Φ_F(τ)`, `Φ_F(0) = I`.
Then `Φ_F(τ)` is invertible on `[0, T′)`, and `Ψ_F(r; τ) = Φ_F(r)Φ_F⁻¹(τ)` (7.9) satisfies
`‖Ψ_F(r; τ)‖op ≤ 1` for every `0 ≤ r ≤ τ < T′`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, Corollary 7.8 and (7.7), (7.9), pp.18–19; invertibility
of `Φ_F` by Liouville's formula, p.20.

**Formalization Note** `R` is `Λ^{1/2}`, the unique symmetric positive definite square root
(footnote 5): `Rᵀ = R`, `R` positive definite, `R * R = Λ`. The paper's maximal interval
`[0, T_max)` is replaced by any initial interval `[0, T′)` on which `(F, H)` solves (4.8).
Invertibility is stated because Lean's matrix inverse is total; (7.9) presupposes it.
`‖·‖op` is the `ℓ²` operator norm. -/
theorem corollary_7_8 {M K D : ℕ} (hM : 1 ≤ M) (γ : Fin (M + 1) → ℝ) (hγ : ∀ n, 0 < γ n)
    (hγN : ∀ n, γ n ≤ γ (Fin.last M)) (Λ : Matrix (Fin K) (Fin K) ℝ) (hΛ : Λ.PosDef)
    (R : Matrix (Fin K) (Fin K) ℝ) (hRsymm : Rᵀ = R) (hRpd : R.PosDef) (hRR : R * R = Λ)
    (α : Matrix (Fin K) (Fin D) ℝ) (ξ : Fin M → Matrix (Fin D) (Fin D) ℝ) (T' : ℝ)
    (F : ℝ → Matrix (Fin M × Fin K) (Fin M × Fin K) ℝ) (H : ℝ → Matrix (Fin M × Fin K) (Fin D) ℝ)
    (hFH : IsRiccatiSolOn γ Λ α ξ (Set.Ico 0 T') F H)
    (ΦF : ℝ → Matrix (Fin M × Fin K) (Fin M × Fin K) ℝ)
    (hΦ : IsLinMatODESol (Set.Ico 0 T') (fun τ => phiCoeff R (F τ)) ΦF) :
    (∀ τ ∈ Set.Ico 0 T', IsUnit (ΦF τ).det) ∧
      ∀ r τ : ℝ, 0 ≤ r → r ≤ τ → τ < T' → opNorm (ΦF r * (ΦF τ)⁻¹) ≤ 1 := by sorry

end LiqPremiaEq
