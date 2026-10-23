-- Prove2me | Theorems.Thm_LagrangeRank_Debias_lemma_A_1
-- name    : LagrangeRank.Debias.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:10:39.998336+00:00
-- url     : https://prove2.me/theorems/c1a736e2-485f-42bb-8962-24c0237a0870
-- title:
--   Lemma A.1, p. 40 — ‖J₁‖∞ ≲ (r₁+r₄)(r₁²+r₂), ‖J₂‖∞ ≲ r₁²r₅, ‖J₃‖∞ ≲ r₁r₃
-- statement:
--   Let $c_1,c_2,L_1,L_2\in\mathbb R$ and $c_3>0$. There are constants $C,\delta>0$, depending only on $c_1,c_2,c_3,L_1,L_2$ and not on the dimension, such that the following holds for every $d$.
--
--   Let $F:\mathbb R^d\to\mathbb R$ be $C^2$ (one realization of the loss $L$), $f:\mathbb R^d\to\mathbb R$ be $C^1$ with $f(\theta^*)=0$, $\widehat\Omega,\Omega^*\in\mathbb R^{d\times d}$, $\widehat\theta,\theta^*\in\mathbb R^d$ and $\rho_1,\dots,\rho_5\ge0$ with $\rho_1+\rho_4\le\delta$. Write $\theta_t=\theta^*+t(\widehat\theta-\theta^*)$. Assume
--
--   1. $\|\widehat\theta-\theta^*\|_\infty\le\rho_1$ and $\|\nabla F(\theta^*)\|_\infty\le\rho_2$;
--   2. $\|\nabla^2F(\theta_t)-\nabla^2F(\theta^*)\|_\infty\le L_1\|\theta_t-\theta^*\|_\infty$ and $\|\nabla f(\theta_t)-\nabla f(\theta^*)\|_1\le L_2\|\theta_t-\theta^*\|_\infty$ for all $t\in[0,1]$;
--   3. $\|\nabla f(\theta^*)\|_1\le c_1$;
--   4. $\|I-\widehat\Omega\nabla^2F(\widehat\theta)\|_\infty\le\rho_3$, $\|\widehat\Omega-\Omega^*\|_\infty\le\rho_4$, $\|\Omega^*\|_\infty\le c_2$, $\nabla f(\theta^*)^\top\Omega^*\nabla f(\theta^*)\ge c_3$ and $\|\Theta^*\|_\infty\le\rho_5$.
--
--   Then for the remainders $J_1,J_2,J_3$ of (A.1), writing $[\,\cdot\,]_\theta$ for the first $d$ coordinates,
--   $$\|[J_1]_\theta\|_\infty\le C(\rho_1+\rho_4)(\rho_1^2+\rho_2),\qquad \|J_2\|_\infty\le C\rho_1^2\rho_5,\qquad \|[J_3]_\theta\|_\infty\le C\rho_1\rho_3,$$
--   and $\|[J_1+J_2+J_3]_\theta\|_\infty\le C\big(\rho_1^2\rho_5+(\rho_1+\rho_4)(\rho_1^2+\rho_2)+\rho_1\rho_3\big)$.
--
--   With $\rho_k\asymp r_k$ these are (A.2)–(A.4) and the bound that follows them in the proof of Theorem 3.1.
--
--   **Formalization Note.** Lemma A.1 is stated "under the conditions of Theorem 3.1"; here it is the deterministic statement for one realization, with the rates replaced by numbers $\rho_k$ and the smallness of $r_1,r_4$ by $\rho_1+\rho_4\le\delta$. The bounds on $J_1$ and $J_3$ are for the first $d$ coordinates (the ones Theorem 3.1 uses): the last coordinate involves the lower-left block of $\widehat\Theta-\Theta^*$ and of $I-\widehat\Theta\widehat\Sigma$, which Assumption 3.4 does not control (see Corollaries 3.1–3.2). The hypothesis $f(\theta^*)=0$ is used in C.1.1 to write $-f(\widehat\theta)+\nabla f(\widehat\theta)^\top(\widehat\theta-\theta^*)$ as a Taylor remainder.
-- source:
--   Liu, Fang, Lu, Lagrangian Inference for Ranking Problems, arXiv:2110.00151v1, p. 40, Lemma A.1, (A.2)–(A.4) and the display following them; proof in Appendix C.1.1, pp. 45–46

import Mathlib
import Definitions.Def_LagrangeRank_Debias_Setting

namespace LagrangeRank.Debias
open Matrix
theorem lemma_A_1 (c1 c2 c3 L1 L2 : ℝ) (hc3 : 0 < c3) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ (d : ℕ) (F f : (Fin d → ℝ) → ℝ) (OmHat OmStar : Matrix (Fin d) (Fin d) ℝ)
        (thetaHat thetaStar : Fin d → ℝ) (ρ1 ρ2 ρ3 ρ4 ρ5 : ℝ),
        ContDiff ℝ 2 F → ContDiff ℝ 1 f → f thetaStar = 0 →
        0 ≤ ρ1 → 0 ≤ ρ2 → 0 ≤ ρ3 → 0 ≤ ρ4 → 0 ≤ ρ5 → ρ1 + ρ4 ≤ δ →
        ‖thetaHat - thetaStar‖ ≤ ρ1 →
        ‖grad F thetaStar‖ ≤ ρ2 →
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
          rowSumNorm (hess F (thetaStar + t • (thetaHat - thetaStar)) - hess F thetaStar)
            ≤ L1 * ‖(thetaStar + t • (thetaHat - thetaStar)) - thetaStar‖) →
        l1Norm (grad f thetaStar) ≤ c1 →
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
          l1Norm (grad f (thetaStar + t • (thetaHat - thetaStar)) - grad f thetaStar)
            ≤ L2 * ‖(thetaStar + t • (thetaHat - thetaStar)) - thetaStar‖) →
        rowSumNorm (1 - OmHat * hess F thetaHat) ≤ ρ3 →
        rowSumNorm (OmHat - OmStar) ≤ ρ4 →
        rowSumNorm OmStar ≤ c2 →
        c3 ≤ grad f thetaStar ⬝ᵥ (OmStar *ᵥ grad f thetaStar) →
        rowSumNorm (thetaBlock OmStar (grad f thetaStar)) ≤ ρ5 →
        ‖fun k => remJ1 (thetaBlock OmHat (grad f thetaHat)) (thetaBlock OmStar (grad f thetaStar))
            (grad F) (hess F thetaHat) f (grad f) thetaHat thetaStar (Sum.inl k)‖
            ≤ C * ((ρ1 + ρ4) * (ρ1 ^ 2 + ρ2)) ∧
        ‖remJ2 (thetaBlock OmStar (grad f thetaStar))
            (grad F) (hess F thetaHat) f (grad f) thetaHat thetaStar‖
            ≤ C * (ρ1 ^ 2 * ρ5) ∧
        ‖fun k => remJ3 (thetaBlock OmHat (grad f thetaHat))
            (borderedHessian (hess F thetaHat) (grad f thetaHat)) thetaHat thetaStar (Sum.inl k)‖
            ≤ C * (ρ1 * ρ3) ∧
        ‖fun k => (remJ1 (thetaBlock OmHat (grad f thetaHat)) (thetaBlock OmStar (grad f thetaStar))
              (grad F) (hess F thetaHat) f (grad f) thetaHat thetaStar
            + remJ2 (thetaBlock OmStar (grad f thetaStar))
              (grad F) (hess F thetaHat) f (grad f) thetaHat thetaStar
            + remJ3 (thetaBlock OmHat (grad f thetaHat))
              (borderedHessian (hess F thetaHat) (grad f thetaHat)) thetaHat thetaStar) (Sum.inl k)‖
            ≤ C * (ρ1 ^ 2 * ρ5 + (ρ1 + ρ4) * (ρ1 ^ 2 + ρ2) + ρ1 * ρ3) := by sorry
end LagrangeRank.Debias
