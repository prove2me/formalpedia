-- Prove2me | Theorems.Thm_MatrixLewis_lemma_3_12
-- name    : MatrixLewis.lemma_3_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:13:51.44513+00:00
-- url     : https://prove2.me/theorems/703b8e77-fa20-4e7b-9168-812ed155aeda
-- title:
--   Lemma 3.12 — reduction to normalized position
-- statement:
--   Throughout, $A_1,\dots,A_m, C$ are real symmetric $n\times n$ matrices, the $A_i$ satisfy Assumption 3.1 (linearly independent, with $\bigcap_i \ker A_i=\{0\}$), and $q>2$ is real; $p=q/(q-2)$ and $p'=q/2$.
--
--   Let $S\succ0$ and $\dot S\in\mathbb S^n$, put $X=S^{-1/2}\dot SS^{-1/2}$, and let $B$ be an invertible $m\times m$ matrix with $BB^\top=M_*(S)$. Let $\varphi'_q$ be the potential of the data $A'_a:=\sum_iB_{ia}B_i(S)$, $a=1,\dots,m$.
--
--   1. The $A'_a$ satisfy Assumption 3.1, and their span is $\mathcal L_S=\operatorname{span}\{B_1(S),\dots,B_m(S)\}$.
--   2. For every $S_1\in\mathbb S^n_{++}$,
--   $$
--   \varphi_q\bigl(S^{1/2}S_1S^{1/2}\bigr)=\varphi'_q(S_1)-\log|\det B| .
--   $$
--   3. For every integer $k\ge1$, $D^k\varphi_q(S)[\dot S,\dots,\dot S]=D^k\varphi'_q(I)[X,\dots,X]$.
--   4. The $A'_a$ are in normalized position; at the slack $I$ their maximizer is $Z_S$, their dual minimizer is $I_m$, and their right weight, left weight and matrix Lewis weight are $W_S$, $\Gamma_S$, $\Lambda_S$.
--
--   Differences from the source:
--   - encoding: Dᵏφ_q(S)[Ṡ,…,Ṡ] → k-th derivative of t ↦ φ_q(S + tṠ) at 0; reason: φ_q is real analytic (Theorem 3.9(iv)), so this is the k-th Fréchet derivative on the diagonal
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), Lemma 3.12, pp.22–23, eq. (23)

import Mathlib
import Definitions.Def_MatrixLewis_Assumption31
import Definitions.Def_MatrixLewis_potential
import Definitions.Def_MatrixLewis_lewisWeight
import Definitions.Def_MatrixLewis_NormalizedPosition
import Definitions.Def_MatrixLewis_lineDeriv

namespace MatrixLewis

/-- **Lemma 3.12** (Normalized position; Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), pp.22–23, eq. (23)). Let `S ≻ 0` and
`Ṡ ∈ Sⁿ`, put `X = S^{−1/2}ṠS^{−1/2}`, and let `B` be an invertible `m × m` matrix with
`BBᵀ = M*(S)`. Let `φ′_q` be the potential of the data `A′_a := ∑ᵢ B_{ia} Bᵢ(S)`.
(i) The data `A′_a` satisfy Assumption 3.1, and their span is `𝓛_S`.
(ii) For every `S₁ ∈ Sⁿ₊₊`, `φ_q(S^{1/2}S₁S^{1/2}) = φ′_q(S₁) − log |det B|`.
(iii) For every integer `k ≥ 1`, `Dᵏφ_q(S)[Ṡ, …, Ṡ] = Dᵏφ′_q(I)[X, …, X]`.
(iv) The data `A′_a` are in normalized position. At the slack `I`, their maximizer is `Z_S`, their
dual minimizer is `I_m`, and their right weight, left weight and matrix Lewis weight are `W_S`,
`Γ_S` and `Λ_S`.

**Formalization Note** `Dᵏ` along the line (`lineDeriv`); `𝓛_S = span{B₁(S), …, B_m(S)}` is
`Submodule.span ℝ (Set.range (scaled A S))`. Standing assumptions of §3 are hypotheses. -/
theorem lemma_3_12 {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (h31 : Assumption31 A) (hq : 2 < q)
    (S Sdot : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef) (hSdot : Sdot.IsHermitian)
    (B : Matrix (Fin m) (Fin m) ℝ) (hB : IsUnit B.det) (hBB : B * B.transpose = dualMin q A S) :
    let X := mpow (-(1 / 2 : ℝ)) S * Sdot * mpow (-(1 / 2 : ℝ)) S
    let A' : Fin m → Matrix (Fin n) (Fin n) ℝ := fun a => ∑ i, B i a • scaled A S i
    -- (i)
    (Assumption31 A' ∧
      Submodule.span ℝ (Set.range A') = Submodule.span ℝ (Set.range (scaled A S))) ∧
    -- (ii)
    (∀ S₁ : Matrix (Fin n) (Fin n) ℝ, S₁.PosDef →
      potential q A (mpow (1 / 2 : ℝ) S * S₁ * mpow (1 / 2 : ℝ) S) =
        potential q A' S₁ - Real.log |B.det|) ∧
    -- (iii)
    (∀ k : ℕ, 1 ≤ k → lineDeriv k (potential q A) S Sdot = lineDeriv k (potential q A') 1 X) ∧
    -- (iv)
    (NormalizedPosition q A' ∧ maximizer q A' 1 = maximizer q A S ∧ dualMin q A' 1 = 1 ∧
      rightWeight q A' 1 = rightWeight q A S ∧ leftWeight q A' 1 = leftWeight q A S ∧
      lewisWeight q A' 1 = lewisWeight q A S) := by sorry

end MatrixLewis
