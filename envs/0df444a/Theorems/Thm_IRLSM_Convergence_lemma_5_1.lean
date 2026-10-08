-- Prove2me | Theorems.Thm_IRLSM_Convergence_lemma_5_1
-- name    : IRLSM.Convergence.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:52:33.750129+00:00
-- url     : https://prove2.me/theorems/2fad4ba8-ce96-4556-8d01-615887e5df14
-- title:
--   Lemma 5.1 — the weighted least squares minimizer $\bar X=(\mathcal W^{-1}\circ\mathcal S^*\circ[\mathcal S\circ\mathcal W^{-1}\circ\mathcal S^*]^{-1})(\mathscr M)$
-- statement:
--   Let $W=W^{\mathsf T}\succ0$ be an $n\times n$ real matrix, let $\mathcal S:\mathbb R^{n\times p}\to\mathbb R^m$ be onto and $\mathscr M\in\mathbb R^m$. Let $\mathcal W^{-1}(X)=W^{-1}X$ and let $G=\mathcal S\circ\mathcal W^{-1}\circ\mathcal S^*$, the $m\times m$ matrix with entries $G_{ij}=\langle A_i,W^{-1}A_j\rangle$. Then the problem $\min_{\mathcal S(X)=\mathscr M}\mathcal J(X,W)$ has the unique solution
--   $$\bar X=W^{-1}\,\mathcal S^*\big(G^{-1}\mathscr M\big).$$
--
--   This explicit formula is the $X$-update of the IRLS-M algorithm: minimizing $\mathcal J(\cdot,W)$ is a weighted least squares problem.
--
--   **Formalization Note** Matrices are real ($n\times p$, with the paper's standing assumption $n\le p$ where $n\times n$ objects occur); the measurement map is $\mathcal S(X)_l=\langle A_l,X\rangle$ for measurement matrices $A_1,\dots,A_m$, so $\mathcal S^*$ is $u\mapsto\sum_l u_lA_l$ and $\langle\cdot,\cdot\rangle$ is the trace inner product. Surjectivity of $\mathcal S$ is added; the page's inverse $[\mathcal S\circ\mathcal W^{-1}\circ\mathcal S^*]^{-1}$ exists exactly when $\mathcal S$ is onto, and Theorem 6.11 assumes it. The conclusion states that $\bar X$ is feasible, minimizes $\mathcal J(\cdot,W)$ on the feasible set, and is the only minimizer.
-- source:
--   Fornasier, Rauhut, Ward, Low-rank matrix recovery via iteratively reweighted least squares minimization, arXiv:1010.2471v4 (2011), Lemma 5.1, pp. 12–13

import Mathlib
import Definitions.Def_IRLSM_Convergence_Algorithm

open HighDimStat.MatrixRank Matrix

namespace IRLSM.Convergence

/-- **Lemma 5.1.** Let `W = Wᵀ ≻ 0` be an `n × n` matrix and let `S` be onto. Then the minimizer
of `𝒥(X, W)` subject to `S(X) = 𝓜` is unique and equals
`X̄ = (𝒲⁻¹ ∘ S* ∘ [S ∘ 𝒲⁻¹ ∘ S*]⁻¹)(𝓜)`, where `𝒲⁻¹(X) := W⁻¹X`.

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, Lemma 5.1, pp. 12–13.

Formalization Notes: real matrices; `S(X)_l = ⟨A_l, X⟩` (`observationOp`), `S*` is
`observationOpAdjoint`; the `m × m` matrix `G` with entries `⟨A_i, W⁻¹A_j⟩` represents
`S ∘ 𝒲⁻¹ ∘ S*`. Surjectivity of `S` is added: the page's inverse `[S ∘ 𝒲⁻¹ ∘ S*]⁻¹` exists exactly
when `S` is onto, and Theorem 6.11 assumes it. `n ≤ p` is the page's standing assumption (p. 4).
"Is given by" is stated as: `X̄` is feasible, minimizes `𝒥(·, W)` on the feasible set, and is the
only minimizer. -/
theorem lemma_5_1 {n p m : ℕ} (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (M : Fin m → ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (hnp : n ≤ p) (hW : W.PosDef)
    (hS : Function.Surjective (observationOp A)) :
    let G : Matrix (Fin m) (Fin m) ℝ := fun i j => traceInner (A i) (W⁻¹ * A j)
    let Xbar : Matrix (Fin n) (Fin p) ℝ := W⁻¹ * observationOpAdjoint A (G⁻¹ *ᵥ M)
    observationOp A Xbar = M ∧
      (∀ Y : Matrix (Fin n) (Fin p) ℝ, observationOp A Y = M → J Xbar W ≤ J Y W) ∧
      (∀ Y : Matrix (Fin n) (Fin p) ℝ, observationOp A Y = M → J Y W ≤ J Xbar W → Y = Xbar) := by sorry

end IRLSM.Convergence
