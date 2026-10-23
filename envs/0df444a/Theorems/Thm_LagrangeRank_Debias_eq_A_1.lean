-- Prove2me | Theorems.Thm_LagrangeRank_Debias_eq_A_1
-- name    : LagrangeRank.Debias.eq_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:10:28.408092+00:00
-- url     : https://prove2.me/theorems/ee33c255-d3e8-427d-91a2-9d0ec1398064
-- title:
--   Equation (A.1), p. 40 — decomposition of (θ̂ᵈ − θ*; λ) into Θ*(−∇L(θ*); −f(θ*)) + J₁ + J₂ + J₃
-- statement:
--   Let $L,f:\mathbb R^d\to\mathbb R$, $\widehat\Omega,\Omega^*\in\mathbb R^{d\times d}$ and $\widehat\theta,\theta^*\in\mathbb R^d$ with $f(\widehat\theta)=0$. Let $\widehat\Theta=\Theta(\widehat\Omega,\nabla f(\widehat\theta))$ and $\Theta^*=\Theta(\Omega^*,\nabla f(\theta^*))$ be the block-inverse matrices of p. 16, $\widehat\Sigma$ the bordered Hessian (3.6) at $\widehat\theta$, $\widehat\theta^d=\widehat\theta-\widehat\Theta_{11}\nabla L(\widehat\theta)$ the debiased estimator (3.9), and $\lambda$ the multiplier of (3.8). Then
--   $$\begin{pmatrix}\widehat\theta^d-\theta^*\\ \lambda\end{pmatrix}=\Theta^*\begin{pmatrix}-\nabla L(\theta^*)\\-f(\theta^*)\end{pmatrix}+J_1+J_2+J_3,$$
--   where $J_1,J_2,J_3$ are the three remainder vectors displayed in (A.1).
--
--   This is the first step of the proof of Theorem 3.1: it separates the leading score term from three remainders, which Lemma A.1 bounds.
--
--   **Formalization Note.** The identity is pure linear algebra; no differentiability is needed. The hypothesis $f(\widehat\theta)=0$ is the standing assumption $\widehat\theta\in C$ (p. 14), under which (3.9) agrees with the first block of (3.8).
-- source:
--   Liu, Fang, Lu, Lagrangian Inference for Ranking Problems, arXiv:2110.00151v1, p. 40, Equation (A.1) (proof of Theorem 3.1, Appendix A.1)

import Mathlib
import Definitions.Def_LagrangeRank_Debias_Setting

namespace LagrangeRank.Debias
open Matrix
theorem eq_A_1 {d : ℕ} (L f : (Fin d → ℝ) → ℝ) (OmHat OmStar : Matrix (Fin d) (Fin d) ℝ)
    (thetaHat thetaStar : Fin d → ℝ) (hfeas : f thetaHat = 0) :
    Sum.elim (estThetaD L f OmHat thetaHat - thetaStar)
        (fun _ => lam (thetaBlock OmHat (grad f thetaHat)) (grad L thetaHat) (f thetaHat))
      = thetaBlock OmStar (grad f thetaStar) *ᵥ
            Sum.elim (-grad L thetaStar) (fun _ => -f thetaStar)
        + remJ1 (thetaBlock OmHat (grad f thetaHat)) (thetaBlock OmStar (grad f thetaStar))
            (grad L) (hess L thetaHat) f (grad f) thetaHat thetaStar
        + remJ2 (thetaBlock OmStar (grad f thetaStar))
            (grad L) (hess L thetaHat) f (grad f) thetaHat thetaStar
        + remJ3 (thetaBlock OmHat (grad f thetaHat))
            (borderedHessian (hess L thetaHat) (grad f thetaHat)) thetaHat thetaStar := by sorry
end LagrangeRank.Debias
