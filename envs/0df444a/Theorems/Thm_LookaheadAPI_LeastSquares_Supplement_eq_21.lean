-- Prove2me | Theorems.Thm_LookaheadAPI_LeastSquares_Supplement_eq_21
-- name    : LookaheadAPI.LeastSquares.Supplement.eq_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:53:44.342043+00:00
-- url     : https://prove2.me/theorems/5d5ba5e6-df9c-4175-a567-eeb22a4f46e1
-- title:
--   Appendix E, eq. (21) — gradient steps contract the Euclidean distance to the least-squares minimiser by $\alpha_{GD,\gamma}$ per step
-- statement:
--   Consider a run $(\theta_k,J_k,\mu_k,w_k)$ of Algorithm 4 (gradient descent with step size $\gamma\in\mathbb R$ and $\eta$ steps per iteration) under Assumption 1 (every Gram matrix $\Phi_{\mathcal D_k}^\top\Phi_{\mathcal D_k}$ invertible and $\|w_k\|_\infty\le\varepsilon_{PE}$). Fix an iteration $k$ and let $\hat J^{\mu_{k+1}}=T^m_{\mu_{k+1}}T^{H-1}J_k+w_{k+1}$ be its noisy return. Let $\tilde\theta$ be the least-squares solution
--   $$\tilde\theta\in\arg\min_\theta\ \tfrac12\big\|\Phi_{\mathcal D_k}\theta-\mathcal P_{\mathcal D_k}\hat J^{\mu_{k+1}}\big\|_2^2 ,$$
--   and let $\theta_{k+1,\ell}$, $\ell=0,\dots,\eta$, be the gradient iterates of the iteration, starting from $\theta_{k+1,0}=\theta_k$. With $\alpha_{GD,\gamma}=\sup_j\max_i|1-\gamma\lambda_i(\Phi_{\mathcal D_j}^\top\Phi_{\mathcal D_j})|$, every gradient step satisfies
--   $$\|\theta_{k+1,\ell}-\tilde\theta\|_2\le\alpha_{GD,\gamma}\,\|\theta_{k+1,\ell-1}-\tilde\theta\|_2\qquad(\ell=1,\dots,\eta),$$
--   and consequently
--   $$\|\theta_{k+1}-\tilde\theta\|_2\le\alpha_{GD,\gamma}^\eta\,\|\theta_k-\tilde\theta\|_2 .$$
--
--   No condition on $\gamma$ is assumed: when $\alpha_{GD,\gamma}\ge1$ the bound holds but is not a contraction. This is the first step of the paper's derivation of the error recursion of Algorithm 4 (Appendix E), which in turn gives Theorem 2.
--
--   **Formalization Note** $\tilde\theta$ is any minimiser of the objective (unique under Assumption 1), stated through the minimality inequality. The norm $\|\cdot\|_2$ is written out as $(\sum_i\theta_i^2)^{1/2}$.
--
--   Differences from the source:
--   - reading: (21) is printed for $\theta_k$ obtained from $\theta_{k-1}$ with $\tilde\theta^{\mu_k}$ defined through $\Phi_{\mathcal D_k}$, $\mathcal P_k$ → Lean states the step from $\theta_k$ to $\theta_{k+1}$ with the evaluation set $\mathcal D_k$, policy $\mu_{k+1}$ and noise $w_{k+1}$; reason: the gradient steps that produce $\theta_{k+1}$ use $\mathcal D_k$ (Algorithm 4, Step 4; the proof on p. 24 writes $\Phi_{\mathcal D_{k-1}}$ for the step producing $\theta_k$), and the published base mission indexes iterations the same way.
--   - reading: $\tilde\theta^{\mu_k}:=\arg\min_\theta\frac12\|\Phi_{\mathcal D_k}\theta-\mathcal P_k(\cdot)\|_2^2$ → any $\tilde\theta$ satisfying the minimality inequality; reason: under Assumption 1 the minimiser is unique, so this is the same point.
--   - encoding: $\lambda_i$, the $i$-th largest eigenvalue → Mathlib's eigenvalues of the symmetric Gram matrix in no particular order; reason: only the maximum over $i$ enters, which does not depend on the order.
-- source:
--   arXiv:2109.13419v7, pp. 23–25, Appendix E, eq. (21) (θ̃^{μ_k} defined on p. 23 with eq. (20); α_GD,γ on p. 24)

import Mathlib
import Definitions.Def_LookaheadAPI_LeastSquares_MDP
import Definitions.Def_LookaheadAPI_LeastSquares_LSOperator
import Definitions.Def_LookaheadAPI_LeastSquares_Algorithms
import Definitions.Def_LookaheadAPI_LeastSquares_Supplement_Algorithm4
import Definitions.Def_LookaheadAPI_LeastSquares_Supplement_GDConstants
open Matrix

namespace LookaheadAPI.LeastSquares.Supplement

/-- Appendix E, eq. (21) (arXiv:2109.13419v7, pp. 23–25): in a run of Algorithm 4 under
Assumption 1, let `θ̃` be a minimiser of the least-squares objective
`∑_{i ∈ 𝒟_k} ((Φθ)(i) − Ĵ^{μ_{k+1}}(i))²` of iteration `k` (the paper's `θ̃^{μ_{k+1}}`, unique under
Assumption 1). Then every gradient step contracts the Euclidean distance to `θ̃` by `α_{GD,γ}`,
`‖θ_{k+1,ℓ} − θ̃‖_2 ≤ α_{GD,γ} ‖θ_{k+1,ℓ−1} − θ̃‖_2` for `ℓ = 1, …, η`, and
`‖θ_{k+1} − θ̃‖_2 ≤ α_{GD,γ}^η ‖θ_k − θ̃‖_2`. Here `θ_{k+1,ℓ}` is the `ℓ`-fold gradient iterate
from `θ_k`. No condition on the step size `γ` is assumed. -/
theorem eq_21 {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A]
    [DecidableEq A] [Nonempty A] (M : MDP S A) {d : ℕ} (Φ : Matrix S (Fin d) ℝ)
    (D : ℕ → Finset S) (m H : ℕ) (hH : 1 ≤ H) (εLA εPE γ : ℝ) (η : ℕ)
    (J : ℕ → S → ℝ) (μ : ℕ → S → A) (w : ℕ → S → ℝ) (θ : ℕ → Fin d → ℝ)
    (hA1 : Assumption1 Φ D w εPE)
    (hrun : IsRunAlg4 M Φ D m H εLA γ η J μ w θ) (k : ℕ) (θt : Fin d → ℝ)
    (hθt : ∀ θ' : Fin d → ℝ,
      ∑ i ∈ D k, ((Φ *ᵥ θt) i - noisyReturn M m H (J k) (μ (k + 1)) (w (k + 1)) i) ^ 2 ≤
        ∑ i ∈ D k, ((Φ *ᵥ θ') i - noisyReturn M m H (J k) (μ (k + 1)) (w (k + 1)) i) ^ 2) :
    (∀ ℓ : ℕ, ℓ < η →
      norm2 ((gdStep Φ (D k) γ (noisyReturn M m H (J k) (μ (k + 1)) (w (k + 1))))^[ℓ + 1] (θ k)
          - θt) ≤
        alphaGD Φ D γ *
          norm2 ((gdStep Φ (D k) γ
            (noisyReturn M m H (J k) (μ (k + 1)) (w (k + 1))))^[ℓ] (θ k) - θt)) ∧
    norm2 (θ (k + 1) - θt) ≤ alphaGD Φ D γ ^ η * norm2 (θ k - θt) := by sorry

end LookaheadAPI.LeastSquares.Supplement
