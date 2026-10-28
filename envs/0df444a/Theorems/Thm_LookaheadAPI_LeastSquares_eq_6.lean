-- Prove2me | Theorems.Thm_LookaheadAPI_LeastSquares_eq_6
-- name    : LookaheadAPI.LeastSquares.eq_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T20:53:48.155848+00:00
-- url     : https://prove2.me/theorems/af8c3e3a-5f00-4f71-bff6-7e5e03b10f27
-- title:
--   Section 3.1, eq. (6) — closed form $J_{k+1}=\mathcal M_{k+1}\hat J^{\mu_{k+1}}$ of the least-squares step
-- statement:
--   Consider a run $(J_k,\mu_k,w_k,\theta_k)$ of Algorithm 2 with feature matrix $\Phi\in\mathbb R^{|\mathcal S|\times d}$ and evaluation sets $\mathcal D_k$, and suppose the rank part of Assumption 1 holds: $\operatorname{rank}\{\phi(i)\}_{i\in\mathcal D_k}=d$ for every $k$. Then for every $k$,
--   $$J_{k+1}=\Phi\theta_{k+1}=\Phi(\Phi_{\mathcal D_k}^\top\Phi_{\mathcal D_k})^{-1}\Phi_{\mathcal D_k}^\top\mathcal P_k\,\hat J^{\mu_{k+1}},$$
--   where $\hat J^{\mu_{k+1}}(i)=T^m_{\mu_{k+1}}T^{H-1}(J_k)(i)+w_{k+1}(i)$ is the noisy $m$-step return.
--
--   The identity turns the least-squares step into the linear operator $\mathcal M_{k+1}=\Phi(\Phi_{\mathcal D_k}^\top\Phi_{\mathcal D_k})^{-1}\Phi_{\mathcal D_k}^\top\mathcal P_k$, whose sup-norm $\delta_{FV}$ governs the convergence of Algorithm 2.
--
--   **Formalization Note** $\hat J^{\mu_{k+1}}$ is written at every state; $\mathcal P_k$ reads only its entries on $\mathcal D_k$, so the values elsewhere do not matter (the paper extends it by $T^m_{\mu_{k+1}}T^{H-1}J_k$).
-- source:
--   arXiv:2109.13419v7, p. 10, Section 3.1, eq. (6)

import Mathlib
import Definitions.Def_LookaheadAPI_LeastSquares_MDP
import Definitions.Def_LookaheadAPI_LeastSquares_LSOperator
import Definitions.Def_LookaheadAPI_LeastSquares_Algorithms

namespace LookaheadAPI.LeastSquares

open Matrix

/-- Section 3.1, eq. (6) (p. 10): under the rank condition of Assumption 1, every run of
Algorithm 2 satisfies `J_{k+1} = Φθ_{k+1} = Φ(Φ_{𝒟_k}^⊤Φ_{𝒟_k})^{-1}Φ_{𝒟_k}^⊤𝒫_k Ĵ^{μ_{k+1}}`. -/
theorem eq_6 {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A]
    [DecidableEq A] [Nonempty A] (M : MDP S A) {d : ℕ} (Φ : Matrix S (Fin d) ℝ)
    (D : ℕ → Finset S) (m H : ℕ) (εLA : ℝ)
    (J : ℕ → S → ℝ) (μ : ℕ → S → A) (w : ℕ → S → ℝ) (θ : ℕ → Fin d → ℝ)
    (hrank : ∀ k : ℕ, (gram Φ (D k)).det ≠ 0)
    (hrun : IsRunAlg2 M Φ D m H εLA J μ w θ) (k : ℕ) :
    J (k + 1) = Φ *ᵥ θ (k + 1) ∧
    Φ *ᵥ θ (k + 1) = lsOp Φ (D k) *ᵥ noisyReturn M m H (J k) (μ (k + 1)) (w (k + 1)) := by sorry

end LookaheadAPI.LeastSquares
