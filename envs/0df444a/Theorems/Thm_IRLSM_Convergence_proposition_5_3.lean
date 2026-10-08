-- Prove2me | Theorems.Thm_IRLSM_Convergence_proposition_5_3
-- name    : IRLSM.Convergence.proposition_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:52:38.073123+00:00
-- url     : https://prove2.me/theorems/271117b7-9a77-44e1-9717-24a2195e84a5
-- title:
--   Proposition 5.3 — $\arg\min_{0\prec W\preceq\varepsilon^{-1}I}\mathcal J(X,W)=U\Sigma_\varepsilon^{-1}U^*$
-- statement:
--   Let $X=U\Sigma V^{\mathsf T}$ with $\Sigma=\operatorname{diag}(\sigma_1,\dots,\sigma_n)$, and let $\varepsilon>0$. Then the minimization of $\mathcal J(X,W)$ over the symmetric matrices $W$ with $0\prec W\preceq\varepsilon^{-1}I$ has the unique solution
--   $$\bar W=U\Sigma_\varepsilon^{-1}U^{\mathsf T},\qquad \Sigma_\varepsilon=\operatorname{diag}(\max\{\sigma_j,\varepsilon\}).$$
--
--   This identifies the weight update (2.12) of IRLS-M as an exact minimization of $\mathcal J$ in $W$, so the algorithm is an alternating minimization of $\mathcal J$.
--
--   **Formalization Note** Matrices are real ($n\times p$, with the paper's standing assumption $n\le p$ where $n\times n$ objects occur); the measurement map is $\mathcal S(X)_l=\langle A_l,X\rangle$ for measurement matrices $A_1,\dots,A_m$, so $\mathcal S^*$ is $u\mapsto\sum_l u_lA_l$ and $\langle\cdot,\cdot\rangle$ is the trace inner product. $\bar W$ is the IRLS-M weight with parameter $\varepsilon$ (the function $t\mapsto1/\max\{\sqrt t,\varepsilon\}$ of $XX^{\mathsf T}$). The arg min is stated as: $\bar W$ is admissible, minimizes $\mathcal J(X,\cdot)$ over the admissible set, and is the only minimizer there.
-- source:
--   Fornasier, Rauhut, Ward, Low-rank matrix recovery via iteratively reweighted least squares minimization, arXiv:1010.2471v4 (2011), Proposition 5.3, (5.8), p. 14

import Mathlib
import Definitions.Def_IRLSM_Convergence_Algorithm

open HighDimStat.MatrixRank Matrix

namespace IRLSM.Convergence

/-- **Proposition 5.3.** Let `X = U Σ Vᵀ` with `Σ = diag(σ_1, …, σ_n)` and let `ε > 0`. Then the
minimization of `𝒥(X, W)` over `0 ≺ W = Wᵀ ⪯ ε⁻¹ I` has the unique solution
`W̄ = U Σ_ε⁻¹ Uᵀ`, with `Σ_ε = diag(max{σ_j, ε})`.

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, Proposition 5.3, (5.8), p. 14.

Formalization Notes: real matrices. `W̄` is `weight ε X`, the function `t ↦ (max{√t, ε})⁻¹` of
`X Xᵀ = U Σ² Uᵀ`, which is `U Σ_ε⁻¹ Uᵀ` for every choice of `U`. "arg min … = W̄" is stated as:
`W̄` is admissible (`W̄ ≻ 0`, `ε⁻¹ I − W̄ ⪰ 0`), minimizes `𝒥(X, ·)` over the admissible set, and
is the only minimizer there. `n ≤ p` is the page's standing assumption (p. 4). -/
theorem proposition_5_3 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (ε : ℝ) (hnp : n ≤ p)
    (hε : 0 < ε) :
    (weight ε X).PosDef ∧
      (ε⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ) - weight ε X).PosSemidef ∧
      (∀ W : Matrix (Fin n) (Fin n) ℝ, W.PosDef →
        (ε⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ) - W).PosSemidef → J X (weight ε X) ≤ J X W) ∧
      (∀ W : Matrix (Fin n) (Fin n) ℝ, W.PosDef →
        (ε⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ) - W).PosSemidef → J X W ≤ J X (weight ε X) →
          W = weight ε X) := by sorry

end IRLSM.Convergence
