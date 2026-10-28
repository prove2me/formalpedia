-- Prove2me | Theorems.Thm_MatrixAnalytic_ProductForm_independence_iff_rate_eigen
-- name    : MatrixAnalytic.ProductForm.independence_iff_rate_eigen
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:49:22.91574+00:00
-- url     : https://prove2.me/theorems/0f605508-4c68-41ac-ab8c-f4532d2779e1
-- title:
--   Theorem 15.1.1 — level and phase are independent iff θR = ηθ and θ(B + ηA₂) = 0
-- statement:
--   Let $Q$ be the generator of a continuous-time QBD,
--   $$Q=\begin{bmatrix} B & A_0 & & \\ A_2 & A_1 & A_0 & \\ & A_2 & A_1 & \ddots \\ & & \ddots & \ddots\end{bmatrix},$$
--   on a countable (possibly infinite) set of phases, irreducible and regular, and let $R$ be its rate matrix (the rate of sojourn in $\ell(n+1)$ per unit local time of $\ell(n)$, Theorem 6.4.1).
--
--   The process is positive recurrent and the level is independent of the phase in steady state (its stationary distribution has the form $\pi_n=\alpha_nv$ for a probability vector $v$ and a probability density $\{\alpha_n\}$) if and only if there exist a positive vector $\boldsymbol\theta$ with $\boldsymbol\theta\mathbf 1=1$ and a scalar $0<\eta<1$ such that
--   $$\boldsymbol\theta R=\eta\boldsymbol\theta \tag{15.1}$$
--   and
--   $$\boldsymbol\theta(B+\eta A_2)=\mathbf 0. \tag{15.2}$$
--   Then the stationary distribution is
--   $$\pi_n=(1-\eta)\eta^n\boldsymbol\theta,\qquad n\ge 0 .$$
--
--   The theorem says that independence of level and phase forces a geometric level marginal, and characterizes it by an eigenvector condition on $R$ together with a boundary condition.
--
--   **Formalization Note** "Positive vector" means $\theta_i>0$ for every phase $i$, and $\boldsymbol\theta\mathbf 1=1$ is a convergent sum. $R$ is the probabilistic rate matrix taken at level $0$ (it is the same at every level by Theorem 6.4.1), with entries in $[0,+\infty]$, and (15.1) is the identity $\sum_i\theta_iR_{ij}=\eta\theta_j$ computed there. (15.2) is the convergent sum $\sum_i\theta_i(B_{ij}+\eta(A_2)_{ij})=0$ for each $j$. The final clause is stated for every $\boldsymbol\theta,\eta$ satisfying the conditions and every stationary probability vector $\pi$ ($\pi Q=0$).
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 296, Theorem 15.1.1

import Mathlib
import Definitions.Def_MatrixAnalytic_ProductForm_Chain
import Definitions.Def_MatrixAnalytic_ProductForm_QBD

open scoped ENNReal

namespace MatrixAnalytic.ProductForm

/-- Theorem 15.1.1 (p. 296). An irreducible, regular continuous-time QBD with generator `Q` of
the form (6.19) is positive recurrent with level independent of phase in steady state if and
only if there are a positive vector `θ` with `θ1 = 1` and a scalar `0 < η < 1` with
`θR = ηθ` (15.1) and `θ(B + ηA₂) = 0` (15.2); `R` is the rate matrix of Theorem 6.4.1 (taken at
level `0`, computed in `ℝ≥0∞`). Then the stationary distribution is `π_n = (1 − η)ηⁿθ`. -/
theorem independence_iff_rate_eigen {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hQ : IsGeneratorC (qbdQ B A₀ A₁ A₂))
    (hirr : IrreducibleCT (qbdQ B A₀ A₁ A₂))
    (hreg : RegularCT (qbdQ B A₀ A₁ A₂)) :
    (((∀ x : ℕ × ι, PositiveRecurrentCT (qbdQ B A₀ A₁ A₂) x) ∧
        ∃ π : ℕ × ι → ℝ, IsStationaryCT (qbdQ B A₀ A₁ A₂) π ∧ LevelPhaseIndependent π) ↔
      ∃ (θ : ι → ℝ) (η : ℝ), (∀ i, 0 < θ i) ∧ HasSum θ 1 ∧ 0 < η ∧ η < 1 ∧
        (∀ j, ∑' i, ENNReal.ofReal (θ i) * rateR (qbdQ B A₀ A₁ A₂) 0 i j =
          ENNReal.ofReal (η * θ j)) ∧
        (∀ j, HasSum (fun i => θ i * (B i j + η * A₂ i j)) 0)) ∧
    ∀ (θ : ι → ℝ) (η : ℝ), (∀ i, 0 < θ i) → HasSum θ 1 → 0 < η → η < 1 →
      (∀ j, ∑' i, ENNReal.ofReal (θ i) * rateR (qbdQ B A₀ A₁ A₂) 0 i j =
        ENNReal.ofReal (η * θ j)) →
      (∀ j, HasSum (fun i => θ i * (B i j + η * A₂ i j)) 0) →
      ∀ π : ℕ × ι → ℝ, IsStationaryCT (qbdQ B A₀ A₁ A₂) π →
        ∀ n i, π (n, i) = (1 - η) * η ^ n * θ i := by sorry

end MatrixAnalytic.ProductForm
