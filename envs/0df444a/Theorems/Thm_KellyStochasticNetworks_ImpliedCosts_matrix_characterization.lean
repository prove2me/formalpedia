-- Prove2me | Theorems.Thm_KellyStochasticNetworks_ImpliedCosts_matrix_characterization
-- name    : KellyStochasticNetworks.ImpliedCosts.matrix_characterization
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:48:19.113978+00:00
-- url     : https://prove2.me/theorems/aa28e8f0-5854-44ab-b86d-4fb4bed76d9b
-- title:
--   Exercise 4.9 — matrix characterization and unique implied costs
-- statement:
--   Consider a finite loss network with integer demands $A_{jr}\ge0$, positive offered traffic $\nu_r$, positive integer capacities $C_j$, real call values $w_r$, and at least one route using each link. Let $B$ be the physical Erlang fixed point, $\lambda_r=\nu_r\prod_j(1-B_j)^{A_{jr}}$, $q_j=\sum_rA_{jr}\lambda_r$, $\rho_j=q_j/(1-B_j)$, and $\delta_j=\rho_j[E(\rho_j,C_j-1)-E(\rho_j,C_j)]$. Then $q_j>0$ and $0\le\delta_j<1$ for every link.
--
--   Set $\Lambda=\operatorname{diag}(\lambda_r)$, $\Gamma=\operatorname{diag}(\delta_j/[(1-\delta_j)q_j])$, and $H=\Gamma^{1/2}$. For any route-surplus vector $s$ and row vector of link costs $c$, equations (4.7) and (4.8) are equivalent to
--   $$s_r=w_r-\sum_jc_jA_{jr},\qquad c(I+A\Lambda A^T\Gamma)=w\Lambda A^T\Gamma.$$
--   The symmetric matrix $Q=I+HA\Lambda A^TH$ is positive definite and invertible. The unique solution of the local equations is
--   $$c=c_*=w\Lambda A^THQ^{-1}H,\qquad s_r=w_r-\sum_j(c_*)_jA_{jr}.$$
--   This gives the algebraic characterization of the costs used in the revenue-sensitivity theorem.
--
--   **Formalization Note** The lower-case diagonal matrices of the source are written $\Lambda,\Gamma$ to distinguish them from their diagonal vectors. The fixed point and all coefficients are computed from the network data. The denominator bounds and matrix invertibility are conclusions, not hypotheses that assume away the exercise. Empty link sets are permitted; a nonempty link set with no routes is excluded by the used-link condition.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed pp. 106–107 (PDF pp. 114–115), Exercise 4.9; https://doi.org/10.1017/CBO9781139565363

import Definitions.Def_KellyStochasticNetworks_ImpliedCosts_Model

namespace KellyStochasticNetworks.ImpliedCosts

/-- Exercise 4.9, including the equivalence, positive definiteness, invertibility,
and explicit unique solution. All quantities are computed from the network data. -/
theorem matrix_characterization {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (w ν : Fin R → ℝ) (C : Fin J → ℕ)
    (hν : ∀ r, 0 < ν r) (hC : ∀ j, 1 ≤ C j)
    (hused : ∀ j, ∃ r, 0 < A j r) :
    let B := blocking A ν (fun j => (C j : ℝ))
    let lam := carried A ν B
    let δ := improvement A ν C B
    let G := Matrix.diagonal (gamma A lam δ)
    let M := incidence A
    let Λ := Matrix.diagonal lam
    let Q := symmetricCostMatrix A lam δ
    let cStar := explicitCosts A w lam δ
    (∀ j, 0 < linkLoad A lam j ∧ 0 ≤ δ j ∧ δ j < 1) ∧
    (∀ (s : Fin R → ℝ) (c : Fin J → ℝ),
      CostSystem A w lam δ s c ↔
        s = surplus A w c ∧
          Matrix.vecMul c (1 + M * Λ * M.transpose * G) =
            Matrix.vecMul w (Λ * M.transpose * G)) ∧
    Q.PosDef ∧ IsUnit Q ∧
    (∀ (s : Fin R → ℝ) (c : Fin J → ℝ),
      CostSystem A w lam δ s c ↔ s = surplus A w cStar ∧ c = cStar) := by sorry

end KellyStochasticNetworks.ImpliedCosts
