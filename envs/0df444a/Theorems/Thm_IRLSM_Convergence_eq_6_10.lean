-- Prove2me | Theorems.Thm_IRLSM_Convergence_eq_6_10
-- name    : IRLSM.Convergence.eq_6_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:52:41.393794+00:00
-- url     : https://prove2.me/theorems/9cc1cd38-ee57-4f8c-a231-d3be59597e48
-- title:
--   (6.10) — $\bar X$ minimizes $\mathcal J_\varepsilon$ on $\{\mathcal S(X)=\mathscr M\}$ iff $\langle W\bar X,H\rangle=0$ on $\ker\mathcal S$, $W=[((\bar X\bar X^*)^{1/2})_\varepsilon]^{-1}$
-- statement:
--   Let $\varepsilon>0$ and let $\bar X$ satisfy $\mathcal S(\bar X)=\mathscr M$. Put $W=\big[((\bar X\bar X^{\mathsf T})^{1/2})_\varepsilon\big]^{-1}$, where $Z_\varepsilon$ is the $\varepsilon$-stabilization (2.3). Then $\bar X$ minimizes $\mathcal J_\varepsilon$ subject to $\mathcal S(X)=\mathscr M$ if and only if
--   $$\langle W\bar X,H\rangle=0\quad\text{for all }H\in\ker\mathcal S .$$
--
--   This optimality condition identifies the limit points of IRLS-M with minimizers of $\mathcal J_\varepsilon$ when $\varepsilon_\ell$ does not tend to $0$.
--
--   **Formalization Note** Matrices are real ($n\times p$, with the paper's standing assumption $n\le p$ where $n\times n$ objects occur); the measurement map is $\mathcal S(X)_l=\langle A_l,X\rangle$ for measurement matrices $A_1,\dots,A_m$, so $\mathcal S^*$ is $u\mapsto\sum_l u_lA_l$ and $\langle\cdot,\cdot\rangle$ is the trace inner product. $W$ is the IRLS-M weight of $\bar X$ with parameter $\varepsilon$. The page reaches the condition through the gradient of $\mathcal J_\varepsilon$ (Propositions 7.3–7.4); only the resulting equivalence is stated.
-- source:
--   Fornasier, Rauhut, Ward, Low-rank matrix recovery via iteratively reweighted least squares minimization, arXiv:1010.2471v4 (2011), proof of Theorem 6.11(ii), (6.10), p. 22

import Mathlib
import Definitions.Def_IRLSM_Convergence_Algorithm

open HighDimStat.MatrixRank Matrix

namespace IRLSM.Convergence

/-- **Optimality condition (6.10) for `𝒥_ε`.** Let `ε > 0` and let `X̄` be feasible (`S(X̄) = 𝓜`).
Then `X̄` minimizes `𝒥_ε` subject to `S(X) = 𝓜` if and only if `⟨W X̄, H⟩ = 0` for all
`H ∈ ker S`, where `W = [((X̄ X̄ᵀ)^{1/2})_ε]⁻¹`.

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, proof of Theorem 6.11(ii), (6.10), p. 22.

Formalization Notes: real matrices; `W = [((X̄X̄ᵀ)^{1/2})_ε]⁻¹` is `weight ε X̄` (the
`ε`-stabilization (2.3) of `(X̄X̄ᵀ)^{1/2}`, inverted). The page passes through `∇𝒥_ε` (Propositions
7.3–7.4); only the resulting equivalence is stated. `n ≤ p` is the page's standing assumption
(p. 4); `𝒥_ε` sums the `n` singular values. -/
theorem eq_6_10 {n p m : ℕ} (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (M : Fin m → ℝ) (ε : ℝ)
    (Xbar : Matrix (Fin n) (Fin p) ℝ) (hnp : n ≤ p) (hε : 0 < ε)
    (hXbar : observationOp A Xbar = M) :
    (∀ Y : Matrix (Fin n) (Fin p) ℝ, observationOp A Y = M → Jeps ε Xbar ≤ Jeps ε Y) ↔
      ∀ H : Matrix (Fin n) (Fin p) ℝ, observationOp A H = 0 →
        traceInner (weight ε Xbar * Xbar) H = 0 := by sorry

end IRLSM.Convergence
