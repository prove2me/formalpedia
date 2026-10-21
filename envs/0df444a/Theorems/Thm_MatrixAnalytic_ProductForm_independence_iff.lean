-- Prove2me | Theorems.Thm_MatrixAnalytic_ProductForm_independence_iff
-- name    : MatrixAnalytic.ProductForm.independence_iff
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:49:37.821561+00:00
-- url     : https://prove2.me/theorems/20d070d2-c8f2-4c4b-b5c3-93b5fa7f97d5
-- title:
--   Theorem 15.1.3 — level and phase are independent iff θ(A₀ + ηA₁ + η²A₂) = 0 and θ(B + ηA₂) = 0
-- statement:
--   Let $Q$ be the generator of a continuous-time QBD with blocks $B, A_0, A_1, A_2$ on a countable (possibly infinite) set of phases, as in (6.19): $A_0$ and $A_2$ nonnegative, $A_1$ and $B$ with nonnegative off-diagonal and strictly negative diagonal entries, zero row sums; assume the process irreducible and regular.
--
--   The process is positive recurrent and the level and phase are independent in steady state (its stationary distribution has the form $\pi_n=\alpha_nv$ for a probability vector $v$ and a probability density $\{\alpha_n\}$) if and only if there exist a positive vector $\boldsymbol\theta$ with $\boldsymbol\theta\mathbf 1=1$ and a scalar $\eta$ with $0<\eta<1$ such that
--   $$\boldsymbol\theta(A_0+\eta A_1+\eta^2A_2)=\mathbf 0 \tag{15.5}$$
--   and
--   $$\boldsymbol\theta(B+\eta A_2)=\mathbf 0 .$$
--   Then the stationary distribution is
--   $$\pi_n=(1-\eta)\eta^n\boldsymbol\theta,\qquad n\ge 0 .$$
--
--   Unlike Theorem 15.1.1, the criterion involves only the blocks of the generator and not the rate matrix $R$, so it can be checked directly; Section 15.2 applies it to Jackson networks, where the phase set is infinite.
--
--   **Formalization Note** "Positive vector" means $\theta_i>0$ for every phase $i$; $\boldsymbol\theta\mathbf 1=1$ and the two vector equations are convergent sums over the phases, $\sum_i\theta_i\big((A_0)_{ij}+\eta(A_1)_{ij}+\eta^2(A_2)_{ij}\big)=0$ and $\sum_i\theta_i\big(B_{ij}+\eta(A_2)_{ij}\big)=0$ for each $j$. Positive recurrence is the return-time notion and regularity the non-explosion of the file `Chain`; the stationary vector solves $\pi Q=0$. The final clause is stated for every $\boldsymbol\theta,\eta$ satisfying the conditions and every stationary probability vector $\pi$. The phase set is not assumed finite.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, pp. 297–298, Theorem 15.1.3

import Mathlib
import Definitions.Def_MatrixAnalytic_ProductForm_Chain
import Definitions.Def_MatrixAnalytic_ProductForm_QBD

namespace MatrixAnalytic.ProductForm

/-- Theorem 15.1.3 (pp. 297–298). An irreducible, regular continuous-time QBD with generator `Q`
of the form (6.19) is positive recurrent with level and phase independent in steady state if and
only if there are a positive vector `θ` with `θ1 = 1` and a scalar `0 < η < 1` with
`θ(A₀ + ηA₁ + η²A₂) = 0` (15.5) and `θ(B + ηA₂) = 0`. Then the stationary distribution is
`π_n = (1 − η)ηⁿθ`. -/
theorem independence_iff {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hQ : IsGeneratorC (qbdQ B A₀ A₁ A₂))
    (hirr : IrreducibleCT (qbdQ B A₀ A₁ A₂))
    (hreg : RegularCT (qbdQ B A₀ A₁ A₂)) :
    (((∀ x : ℕ × ι, PositiveRecurrentCT (qbdQ B A₀ A₁ A₂) x) ∧
        ∃ π : ℕ × ι → ℝ, IsStationaryCT (qbdQ B A₀ A₁ A₂) π ∧ LevelPhaseIndependent π) ↔
      ∃ (θ : ι → ℝ) (η : ℝ), (∀ i, 0 < θ i) ∧ HasSum θ 1 ∧ 0 < η ∧ η < 1 ∧
        (∀ j, HasSum (fun i => θ i * (A₀ i j + η * A₁ i j + η ^ 2 * A₂ i j)) 0) ∧
        (∀ j, HasSum (fun i => θ i * (B i j + η * A₂ i j)) 0)) ∧
    ∀ (θ : ι → ℝ) (η : ℝ), (∀ i, 0 < θ i) → HasSum θ 1 → 0 < η → η < 1 →
      (∀ j, HasSum (fun i => θ i * (A₀ i j + η * A₁ i j + η ^ 2 * A₂ i j)) 0) →
      (∀ j, HasSum (fun i => θ i * (B i j + η * A₂ i j)) 0) →
      ∀ π : ℕ × ι → ℝ, IsStationaryCT (qbdQ B A₀ A₁ A₂) π →
        ∀ n i, π (n, i) = (1 - η) * η ^ n * θ i := by sorry

end MatrixAnalytic.ProductForm
