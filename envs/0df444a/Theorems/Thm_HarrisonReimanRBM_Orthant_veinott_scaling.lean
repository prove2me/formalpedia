-- Prove2me | Theorems.Thm_HarrisonReimanRBM_Orthant_veinott_scaling
-- name    : HarrisonReimanRBM.Orthant.veinott_scaling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:22:42.376375+00:00
-- url     : https://prove2.me/theorems/cfadeede-7c8a-43ee-876e-578c69ae10cf
-- title:
--   Veinott scaling: a positive diagonal $\Lambda$ with $\|\Lambda^{-1}Q\Lambda\|<1$ (maximal row sum)
-- statement:
--   Let $K\ge1$ and let $Q=(q_{ij})$ be a nonnegative $K\times K$ matrix with zeros on the diagonal and spectral radius strictly less than unity. For a nonnegative matrix $P$ write $\|P\|=\max_i\sum_j p_{ij}$ for its maximal row sum. Then there is a diagonal matrix $\Lambda=\operatorname{diag}(d_1,\dots,d_K)$ with $d_i>0$ for all $i$ such that the nonnegative matrix $Q^*=\Lambda^{-1}Q\Lambda$ satisfies
--   $$\|Q^*\|=\max_{1\le i\le K}\sum_{j=1}^K\frac{q_{ij}\,d_j}{d_i}<1.$$
--
--   This is the first step of the proof of Theorem 1 (the paper cites Veinott (1969), Lemma 3): combined with the rescaling equivalence, it reduces the proof to a matrix of norm less than one.
--
--   **Formalization Note** The statement is as printed, with the maximal **row** sum. The contraction step of the proof needs the maximal **column** sum under the paper's row-vector convention (see the contraction milestone); since $Q^\top$ satisfies the same hypotheses as $Q$, applying this statement to $Q^\top$ yields a positive diagonal $\Lambda'$ with $\Lambda'^{-1}Q\Lambda'$ of maximal column sum $<1$. Spectral radius $<1$ is rendered as $Q^m\to0$.
-- source:
--   Harrison & Reiman, Reflected Brownian Motion on an Orthant, Ann. Probab. 9(2) (1981), p. 304, proof of Theorem 1, first paragraph (citing Veinott (1969), Lemma 3)

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_HarrisonReimanRBM_Orthant_Basic

namespace HarrisonReimanRBM.Orthant

/-- Proof of Theorem 1, p. 304 (Veinott (1969), Lemma 3): for `Q` as in §1 there is a diagonal
matrix `Λ = diag(d)` with positive diagonal elements such that the nonnegative matrix
`Q* = Λ⁻¹QΛ` has maximal row sum `‖Q*‖ < 1`. -/
theorem veinott_scaling {K : ℕ} (hK : 0 < K) (Q : Matrix (Fin K) (Fin K) ℝ)
    (hQ : IsReflectionMatrix Q) :
    ∃ d : Fin K → ℝ, (∀ i, 0 < d i) ∧ maxRowSum (rescaleMatrix d Q) < 1 := by sorry

end HarrisonReimanRBM.Orthant
