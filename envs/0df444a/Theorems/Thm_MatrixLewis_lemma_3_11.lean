-- Prove2me | Theorems.Thm_MatrixLewis_lemma_3_11
-- name    : MatrixLewis.lemma_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:13:54.2532+00:00
-- url     : https://prove2.me/theorems/6f94650c-6c1f-40b0-bdac-31080107bef2
-- title:
--   Lemma 3.11 — Lewis weights have trace $m$
-- statement:
--   Throughout, $A_1,\dots,A_m, C$ are real symmetric $n\times n$ matrices, the $A_i$ satisfy Assumption 3.1 (linearly independent, with $\bigcap_i \ker A_i=\{0\}$), and $q>2$ is real; $p=q/(q-2)$ and $p'=q/2$.
--
--   Let $S\succ0$, write $B_i=B_i(S)$, and let $B$ be an invertible $m\times m$ matrix with $BB^\top=M_*(S)$. The matrices
--   $$
--   V_a:=\sum_iB_{ia}B_iZ_S^{1/2},\qquad a=1,\dots,m,
--   $$
--   are orthonormal in the Frobenius inner product, and $W_S=\sum_aV_a^\top V_a$, $\Gamma_S=\sum_aV_aV_a^\top$. Consequently
--   $$
--   \operatorname{tr}W_S=\operatorname{tr}\Gamma_S=\operatorname{tr}\Lambda_S=m,\quad W_S\preceq2\Lambda_S,\quad \Gamma_S\preceq2\Lambda_S,\quad \Lambda_S\succeq\tfrac12W_S\succ0 .
--   $$
--
--   The trace identity is the source of the barrier parameter $m$.
--
--   Differences from the source:
--   - encoding: P ⪯ Q; Frobenius inner product; B invertible → (Q − P) positive semidefinite; tr(JᵀJ′); det B a unit; reason: standard Lean forms of the same notions
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), Lemma 3.11, p.22, eqs. (20)–(21)

import Mathlib
import Definitions.Def_MatrixLewis_Assumption31
import Definitions.Def_MatrixLewis_lewisWeight

namespace MatrixLewis

/-- **Lemma 3.11** (Lewis weights have trace `m`; Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), p.22, eq. (21)). Let `S ≻ 0`, and let
`B` be an invertible `m × m` matrix with `BBᵀ = M*`. The matrices
`V_a := ∑ᵢ B_{ia} Bᵢ Z_S^{1/2}`, `a = 1, …, m`, are orthonormal in the Frobenius inner product, and
`W_S = ∑_a V_aᵀV_a`, `Γ_S = ∑_a V_aV_aᵀ`. Consequently `tr W_S = tr Γ_S = tr Λ_S = m`,
`W_S ⪯ 2Λ_S`, `Γ_S ⪯ 2Λ_S`, `Λ_S ⪰ ½W_S ≻ 0`.

**Formalization Note** `Bᵢ = Bᵢ(S)`; the Frobenius inner product of real matrices is
`⟨J, J′⟩_F = tr(JᵀJ′)`; `P ⪯ Q` is `(Q − P).PosSemidef`. Standing assumptions of §3 are
hypotheses. -/
theorem lemma_3_11 {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (h31 : Assumption31 A) (hq : 2 < q)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef) (B : Matrix (Fin m) (Fin m) ℝ)
    (hB : IsUnit B.det) (hBB : B * B.transpose = dualMin q A S) :
    let V : Fin m → Matrix (Fin n) (Fin n) ℝ := fun a =>
      (∑ i, B i a • scaled A S i) * mpow (1 / 2 : ℝ) (maximizer q A S)
    let W := rightWeight q A S
    let Γ := leftWeight q A S
    let Λ := lewisWeight q A S
    (∀ a b : Fin m, ((V a).transpose * V b).trace = if a = b then 1 else 0) ∧
    W = ∑ a, (V a).transpose * V a ∧
    Γ = ∑ a, V a * (V a).transpose ∧
    W.trace = m ∧ Γ.trace = m ∧ Λ.trace = m ∧
    ((2 : ℝ) • Λ - W).PosSemidef ∧ ((2 : ℝ) • Λ - Γ).PosSemidef ∧
    (Λ - (1 / 2 : ℝ) • W).PosSemidef ∧ ((1 / 2 : ℝ) • W).PosDef := by sorry

end MatrixLewis
