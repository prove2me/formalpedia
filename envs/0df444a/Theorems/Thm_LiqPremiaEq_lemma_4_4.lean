-- Prove2me | Theorems.Thm_LiqPremiaEq_lemma_4_4
-- name    : LiqPremiaEq.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:03:11.478788+00:00
-- url     : https://prove2.me/theorems/e4f73b44-9f19-4d01-889f-840207f57215
-- title:
--   Lemma 4.4 — the matrix Riccati system (4.8) has a unique global solution and $F\succeq0$ (corrected: c_n ≥ 0)
-- statement:
--   Let $N\ge2$, $\gamma^n>0$ with $\gamma^N=\max_n\gamma^n$, $\Lambda$ symmetric positive definite, $\alpha\in\mathbb R^{K\times D}$, $\xi\in\mathbb R^{(N-1)D\times D}$ and $T>0$. Define $c=(c_1,\dots,c_{N-1})^\top$ with $c_n=\bar\gamma(1/\gamma^n-1/\gamma^N)$. Then:
--
--   1. $c_n\ge0$ for every $n$;
--   2. the initial value problem
--   $$F'=\Gamma\otimes\big(\alpha+(c\otimes I_K)^\top H\big)\big(\alpha+(c\otimes I_K)^\top H\big)^\top-F(I_{N-1}\otimes\Lambda^{-1})F,\quad F(0)=0,$$
--   $$H'=\big(\Gamma\otimes(\alpha+(c\otimes I_K)^\top H)\big)\xi-F(I_{N-1}\otimes\Lambda^{-1})H,\quad H(0)=0\qquad(4.8)$$
--   has a solution $(F,H)$ on $[0,T]$;
--   3. any two solutions on $[0,T]$ coincide on $[0,T]$;
--   4. every solution has $F(\tau)$ positive semidefinite ($b^\top F(\tau)b\ge0$, no symmetry) for $\tau\in[0,T]$.
--
--   This global well-posedness, for any number of agents and assets, is the tool from which Theorem 4.5 builds the equilibrium explicitly.
--
--   Differences from the source:
--   - correction: cₙ := γ̄(1/γⁿ − 1/γᴺ) > 0 → 0 ≤ cₙ; reason: (3.2) allows γⁿ = γᴺ for some n < N; counterexample N = 2, γ¹ = γ² = 1 gives γ̄ = 1/2 and c₁ = 0; the proofs use only ‖c‖
--   - generalization: α, ξ from Assumptions 3.2 and 4.3 (rank α = rank αα⊤ = K, K ≤ D) → α ∈ ℝ^{K×D} and ξ ∈ ℝ^{(N−1)D×D} arbitrary, K and D arbitrary; reason: the proof of Lemma 4.4 uses neither the rank condition nor K ≤ D beyond a constant; the printed case is included
--   - encoding: “a unique global solution (F, H) on [0, T]” → existence of a solution on [0, T] and agreement of any two solutions on [0, T]; reason: the same claim, split into its two parts
--   - reading: positive (semi)definite → IsPSDQuad A: bᵀAb ≥ 0 for all b (IsPDQuad: bᵀAb > 0 for b ≠ 0), no symmetry required; reason: footnotes 10 (p.8) and 19 (p.14): the matrices are not symmetric and the notions are meant without symmetry
--   - encoding: agents n = 1, …, N with N ≥ 2; agent N the most risk-averse (3.2) → agents Fin (M + 1) with 1 ≤ M; agent N is Fin.last M; agents 1, …, N − 1 are Fin M via Fin.castSucc; reason: a relabelling of the same agents
--   - encoding: stacked vectors and matrices in ℝ^{K(N−1)}, ℝ^{K(N−1)×D}, ℝ^{(N−1)D×D}; Kronecker products A ⊗ B, c ⊗ I_K, c ⊗ Λ, 1_{N−1} ⊗ v → index types Fin M × Fin K (resp. Fin M × Fin D), block index first; Mathlib kroneckerMap; c ⊗ B as colKron c B (the Unit column index of a column vector dropped); 1 ⊗ v as onesKron v; reason: the same entries in the same block positions (p.3 convention)
--   - encoding: matrix ODEs on an interval → every entry has the stated derivative within the interval at each of its points (one-sided at the endpoints); reason: entrywise differentiability is differentiability of a matrix function on a finite-dimensional space
-- source:
--   Muhle-Karbe–Shi–Yang, An Equilibrium Model for the Cross-Section of Liquidity Premia, arXiv:2011.13625v1, Lemma 4.4, p.8

import Mathlib
import Definitions.Def_LiqPremiaEq_IsPSDQuad
import Definitions.Def_LiqPremiaEq_IsRiccatiSolOn

open Matrix

namespace LiqPremiaEq

/-- **Lemma 4.4.** Let `cₙ = γ̄(1/γⁿ − 1/γᴺ)`, `n = 1, …, N − 1`. Then `cₙ ≥ 0`; the matrix Riccati
system (4.8),
`F′ = Γ ⊗ (α + (c ⊗ I_K)ᵀH)(α + (c ⊗ I_K)ᵀH)ᵀ − F (I_{N−1} ⊗ Λ⁻¹) F`, `F(0) = 0`,
`H′ = (Γ ⊗ (α + (c ⊗ I_K)ᵀH)) ξ − F (I_{N−1} ⊗ Λ⁻¹) H`, `H(0) = 0`,
has a solution `(F, H)` on `[0, T]`; any two solutions coincide on `[0, T]`; and `F` takes values in
the positive semidefinite matrices.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, Lemma 4.4, p.8.

**Formalization Note** Corrected: the page prints `cₙ > 0`, which fails when `γⁿ = γᴺ` for
some `n < N` (e.g. `N = 2`, `γ¹ = γ² = 1` gives `c₁ = 0`); the correct claim is `cₙ ≥ 0`. `α`
and `ξ` are arbitrary (the rank condition of Assumption 3.2 is not needed). Positive
semidefinite means `bᵀFb ≥ 0` without symmetry (footnote 10). -/
theorem lemma_4_4 {M K D : ℕ} (hM : 1 ≤ M) (γ : Fin (M + 1) → ℝ) (hγ : ∀ n, 0 < γ n)
    (hγN : ∀ n, γ n ≤ γ (Fin.last M)) (Λ : Matrix (Fin K) (Fin K) ℝ) (hΛ : Λ.PosDef)
    (α : Matrix (Fin K) (Fin D) ℝ) (ξ : Fin M → Matrix (Fin D) (Fin D) ℝ) (T : ℝ) (hT : 0 < T) :
    (∀ n, 0 ≤ cvec γ n) ∧
      (∃ F H, IsRiccatiSolOn γ Λ α ξ (Set.Icc 0 T) F H) ∧
      (∀ F₁ H₁ F₂ H₂, IsRiccatiSolOn γ Λ α ξ (Set.Icc 0 T) F₁ H₁ →
        IsRiccatiSolOn γ Λ α ξ (Set.Icc 0 T) F₂ H₂ →
        Set.EqOn F₁ F₂ (Set.Icc 0 T) ∧ Set.EqOn H₁ H₂ (Set.Icc 0 T)) ∧
      (∀ F H, IsRiccatiSolOn γ Λ α ξ (Set.Icc 0 T) F H → ∀ τ ∈ Set.Icc 0 T, IsPSDQuad (F τ)) := by sorry

end LiqPremiaEq
