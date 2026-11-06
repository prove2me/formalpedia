-- Prove2me | Theorems.Thm_MatrixLewis_lemma_3_13
-- name    : MatrixLewis.lemma_3_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:13:34.415068+00:00
-- url     : https://prove2.me/theorems/f3e42f7e-9905-4e9d-b1fc-45af51a29595
-- title:
--   Lemma 3.13 — row operator identities
-- statement:
--   Throughout, $A_1,\dots,A_m, C$ are real symmetric $n\times n$ matrices, the $A_i$ satisfy Assumption 3.1 (linearly independent, with $\bigcap_i \ker A_i=\{0\}$), and $q>2$ is real; $p=q/(q-2)$ and $p'=q/2$.
--
--   1. Let $T$ be a linear map between finite-dimensional real inner-product spaces with $T^\top T$ positive definite. Then for every real $r>-1$,
--   $$
--   T(T^\top T)^rT^\top=(TT^\top)^{r+1}.
--   $$
--   2. Let the data be in normalized position, let $Z=Z_I$, $W=W_I$, $\Gamma=\Gamma_I$, and let $T$ be the row operator of $B_i=B_i(I)$. Then $\Gamma=\sum_iB_iZB_i$, $T^\top T=\sum_iB_i^2=Z^{p-1}$, $Z=(T^\top T)^{p'-1}$, $W=(T^\top T)^{p'}$ and $(TT^\top)^{p'}=TZT^\top$; for $M\in\mathbb S^m$ and $Y\in\mathbb S^n$,
--   $$
--   \operatorname{tr}\bigl(TZT^\top(M\otimes I_n)\bigr)=\operatorname{tr}M,\qquad \operatorname{tr}\bigl(TZT^\top(I_m\otimes Y)\bigr)=\operatorname{tr}(\Gamma Y).
--   $$
--   3. Let $T$ be the row operator of $A_1,\dots,A_m$. For every $S\succ0$ and $M\in\mathbb S^m$,
--   $$
--   H_S^*(M)=S^{-1/2}\,T^\top(M\otimes S^{-1})T\,S^{-1/2}.
--   $$
--
--   Differences from the source:
--   - encoding: a linear map between finite-dimensional real inner-product spaces → a real matrix T : ℝ^κ → ℝ^ι for finite index types, with adjoint the transpose; reason: every such map is a real matrix in orthonormal bases, and the identity is basis-invariant
--   - encoding: ℝᵐ ⊗ ℝⁿ and M ⊗ Y → index type Fin m × Fin n and Matrix.kroneckerMap; reason: same index order as the row operator
--   - encoding: (a), a statement about a linear map with no SDP data → clause (a) of one theorem whose binders carry the data hypotheses of (b) and (c); reason: (a) does not mention the data and those hypotheses are satisfiable (n = m = 0, q = 3), so the clause is the same statement
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), Lemma 3.13, pp.23–24, eqs. (24)–(26)

import Mathlib
import Definitions.Def_MatrixLewis_Assumption31
import Definitions.Def_MatrixLewis_lewisWeight
import Definitions.Def_MatrixLewis_NormalizedPosition
import Definitions.Def_MatrixLewis_rowOp

open scoped Kronecker

namespace MatrixLewis

/-- **Lemma 3.13** (Row operator identities; Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), pp.23–24, eqs. (24)–(26)).
(a) Let `T` be a linear map between finite-dimensional real inner-product spaces with `TᵀT`
positive definite. Then for every real `r > −1`, `T(TᵀT)^r Tᵀ = (TTᵀ)^{r+1}`.
(b) Let the data be in normalized position, let `Z = Z_I`, `W = W_I`, `Γ = Γ_I`, and let `T` be the
row operator of `Bᵢ = Bᵢ(I)`. Then `Γ = ∑ᵢ BᵢZBᵢ`, `TᵀT = ∑ᵢ Bᵢ² = Z^{p−1}`, `Z = (TᵀT)^{p′−1}`,
`W = (TᵀT)^{p′}`, and `(TTᵀ)^{p′} = TZTᵀ`. For `M ∈ Sᵐ` and `Y ∈ Sⁿ`,
`tr(TZTᵀ(M ⊗ Iₙ)) = tr M` and `tr(TZTᵀ(I_m ⊗ Y)) = tr(ΓY)`.
(c) Let `T` be the row operator of `A₁, …, A_m`. For every `S ≻ 0` and `M ∈ Sᵐ`,
`H*_S(M) = S^{−1/2} Tᵀ(M ⊗ S⁻¹)T S^{−1/2}`.

**Formalization Note** In (a), a linear map between finite-dimensional real inner-product spaces
is written, in orthonormal bases, as a real matrix `T : Matrix ι κ ℝ` (from `ℝ^κ` to `ℝ^ι`), and
its adjoint is the transpose; `(TTᵀ)^{r+1}` is the positive semidefinite power (`0^{r+1} = 0`).
Kronecker products `M ⊗ Y` are `Matrix.kroneckerMap` (`⊗ₖ`) with the index order
`Fin m × Fin n` of the row operator. Standing assumptions of §3 are hypotheses of (b) and (c). -/
theorem lemma_3_13 {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (h31 : Assumption31 A) (hq : 2 < q) :
    -- (a)
    (∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (T : Matrix ι κ ℝ),
      (T.transpose * T).PosDef → ∀ r : ℝ, -1 < r →
        T * mpow r (T.transpose * T) * T.transpose = mpow (r + 1) (T * T.transpose)) ∧
    -- (b)
    (NormalizedPosition q A →
      let Z := maximizer q A 1
      let W := rightWeight q A 1
      let Γ := leftWeight q A 1
      let B := scaled A 1
      let T := rowOp B
      Γ = ∑ i, B i * Z * B i ∧
      T.transpose * T = ∑ i, B i * B i ∧
      ∑ i, B i * B i = mpow (pExp q - 1) Z ∧
      Z = mpow (pDual q - 1) (T.transpose * T) ∧
      W = mpow (pDual q) (T.transpose * T) ∧
      mpow (pDual q) (T * T.transpose) = T * Z * T.transpose ∧
      (∀ M : Matrix (Fin m) (Fin m) ℝ, M.IsHermitian →
        (T * Z * T.transpose * (M ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℝ))).trace = M.trace) ∧
      (∀ Y : Matrix (Fin n) (Fin n) ℝ, Y.IsHermitian →
        (T * Z * T.transpose * ((1 : Matrix (Fin m) (Fin m) ℝ) ⊗ₖ Y)).trace = (Γ * Y).trace)) ∧
    -- (c)
    (∀ (S : Matrix (Fin n) (Fin n) ℝ) (M : Matrix (Fin m) (Fin m) ℝ), S.PosDef → M.IsHermitian →
      gramAdj A S M = mpow (-(1 / 2 : ℝ)) S *
        ((rowOp A).transpose * (M ⊗ₖ S⁻¹) * rowOp A) * mpow (-(1 / 2 : ℝ)) S) := by sorry

end MatrixLewis
