-- Prove2me | Theorems.Thm_IRLSM_Convergence_eq_5_4
-- name    : IRLSM.Convergence.eq_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:52:34.183854+00:00
-- url     : https://prove2.me/theorems/3a59e1e6-24a8-4281-8cfb-2a6fa671899d
-- title:
--   (5.4) — optimality of weighted least squares: $\langle W\bar X,H\rangle=0$ for all $H\in\ker\mathcal S$
-- statement:
--   Let $W=W^{\mathsf T}\succ0$ be $n\times n$ and let $\bar X$ satisfy $\mathcal S(\bar X)=\mathscr M$. Then $\bar X$ minimizes $\|W^{1/2}X\|_F^2$ subject to $\mathcal S(X)=\mathscr M$ if and only if
--   $$\langle W\bar X,H\rangle=0\quad\text{for all }H\in\ker\mathcal S,$$
--   and this holds if and only if $W\bar X=\mathcal S^*(\lambda)$ for some $\lambda\in\mathbb R^m$.
--
--   This is the first-order optimality condition used for the $X$-update; it is invoked in Proposition 6.1(iii) and in the proof of Theorem 6.11(ii).
--
--   **Formalization Note** Matrices are real ($n\times p$, with the paper's standing assumption $n\le p$ where $n\times n$ objects occur); the measurement map is $\mathcal S(X)_l=\langle A_l,X\rangle$ for measurement matrices $A_1,\dots,A_m$, so $\mathcal S^*$ is $u\mapsto\sum_l u_lA_l$ and $\langle\cdot,\cdot\rangle$ is the trace inner product. $W^{1/2}$ is the positive definite square root (`cfc Real.sqrt W`). Both forms of (5.4) are stated.
-- source:
--   Fornasier, Rauhut, Ward, Low-rank matrix recovery via iteratively reweighted least squares minimization, arXiv:1010.2471v4 (2011), proof of Lemma 5.1, (5.4), p. 13

import Mathlib
import Definitions.Def_IRLSM_Convergence_Algorithm

open HighDimStat.MatrixRank Matrix

namespace IRLSM.Convergence

/-- **Optimality condition (5.4).** For `W = Wᵀ ≻ 0` and a feasible `X̄` (`S(X̄) = 𝓜`), `X̄`
minimizes `‖W^{1/2} X‖²_F` subject to `S(X) = 𝓜` if and only if `⟨W X̄, H⟩ = 0` for all
`H ∈ ker S`; equivalently, if and only if `W X̄ = S*(λ)` for some `λ ∈ ℝ^m`.

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, proof of Lemma 5.1, (5.4), p. 13.

Formalization Notes: real matrices, so `S*` is `observationOpAdjoint` and `⟨·,·⟩` is
`traceInner`; `W^{1/2}` is `cfc Real.sqrt W`. Both equivalent forms of (5.4) are stated.
`n ≤ p` is the page's standing assumption (p. 4). -/
theorem eq_5_4 {n p m : ℕ} (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (M : Fin m → ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (Xbar : Matrix (Fin n) (Fin p) ℝ) (hnp : n ≤ p)
    (hW : W.PosDef) (hXbar : observationOp A Xbar = M) :
    ((∀ Y : Matrix (Fin n) (Fin p) ℝ, observationOp A Y = M →
        frobeniusNorm (cfc Real.sqrt W * Xbar) ^ 2 ≤ frobeniusNorm (cfc Real.sqrt W * Y) ^ 2) ↔
      ∀ H : Matrix (Fin n) (Fin p) ℝ, observationOp A H = 0 → traceInner (W * Xbar) H = 0) ∧
    ((∀ H : Matrix (Fin n) (Fin p) ℝ, observationOp A H = 0 → traceInner (W * Xbar) H = 0) ↔
      ∃ lam : Fin m → ℝ, observationOpAdjoint A lam = W * Xbar) := by sorry

end IRLSM.Convergence
