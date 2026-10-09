-- Prove2me | Theorems.Thm_HyperbolicBackstepping_Quasilinear_proposition_5_1
-- name    : HyperbolicBackstepping.Quasilinear.proposition_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:22:53.777373+00:00
-- url     : https://prove2.me/theorems/fce0eaf3-31e5-42f0-bda9-9ef1e811a660
-- title:
--   Proposition 5.1, p. 13 — for ‖γ‖_∞ small, V₁ = ∫γᵀDγ satisfies the differential inequality (5.28)
-- statement:
--   Assume the standing hypotheses of §2 with $q\neq0$, a $C^2$ full kernel $K$ solving (3.30)–(3.37) with the coefficients of (4.7), (4.9), and constants $d_1,d_2>0$, $d_1\ne d_2$. Then there are a weight $D$ of the form (3.9) (constants $A,B,\mu>0$), a threshold $\delta_1>0$ and positive constants $\lambda_1,\lambda_2,C_1,C_2,C_3$ such that for every classical solution $(z,a,b)$ of the closed loop (2.1), (4.20), (4.21), with $\gamma=(\alpha,\beta)=\mathcal K[\Phi z]$ and $V_1(t)=\int_0^1\gamma^{\mathsf T}D\gamma\,dx$, and every $t\ge0$ with $\|\gamma(\cdot,t)\|_\infty<\delta_1$,
--   $$\dot V_1\le-\lambda_1V_1-\lambda_2\big(\alpha^2(1,t)+\beta^2(0,t)\big)+C_1V_1^{3/2}+C_2\|\gamma_x\|_\infty V_1+C_3\big(a^2(t)+b^2(t)\big).$$
--
--   This is the $L^2$-level Lyapunov estimate of the proof of Theorem 4.1; the term $C_2\|\gamma_x\|_\infty V_1$ is later controlled through Lemma B.6.
--
--   **Formalization Note** The paper fixes $D$ ("$B=(|q|+K_8)^2A+\lambda_2$ and $A$, $\mu$ as in the proof of Proposition 3.1"); Lean asserts that some $D$ of the form (3.9) works. All constants are chosen after the data and before the solution. The boundary value $\beta(1,t)=\varphi_2(1)(a(t)+b(t))$ carries a factor $\varphi_2(1)$ that the proof's (5.26) omits; it is absorbed in $C_3$. Solutions are $C^2$ (classical), and $\dot V_1$ is the derivative of $t\mapsto V_1(t)$.
-- source:
--   Coron, Vazquez, Krstic and Bastin, Local Exponential H² Stabilization of a 2 × 2 Quasilinear Hyperbolic System Using Backstepping, arXiv:1208.6475v1, p. 13, Proposition 5.1, (5.28)

import Mathlib
import Definitions.Def_HyperbolicBackstepping_Quasilinear_ClosedLoop
import Definitions.Def_HyperbolicBackstepping_Quasilinear_Backstepping

namespace HyperbolicBackstepping.Quasilinear

theorem proposition_5_1 (P : Plant) (hq : P.q ≠ 0)
    (Kuu Kuv Kvu Kvv : ℝ → ℝ → ℝ)
    (hK : IsFullKernel P.ε₁ P.ε₂ P.c₁ P.c₂ P.q Kuu Kuv Kvu Kvv)
    (d₁ d₂ : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd : d₁ ≠ d₂) :
    ∃ A B μ : ℝ, 0 < A ∧ 0 < B ∧ 0 < μ ∧
      ∃ δ₁ : ℝ, 0 < δ₁ ∧
        ∃ l₁ l₂ C₁ C₂ C₃ : ℝ, 0 < l₁ ∧ 0 < l₂ ∧ 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧
          ∀ (z : ℝ → ℝ → Fin 2 → ℝ) (a b : ℝ → ℝ),
            IsClosedLoopSolution P Kvu Kvv d₁ d₂ z a b →
            ∀ t : ℝ, 0 ≤ t →
              supNorm (slice (gam P (Kmat Kuu Kuv Kvu Kvv) z) t) < δ₁ →
              deriv (fun s => V₁ P A B μ (Kmat Kuu Kuv Kvu Kvv) z s) t
                ≤ -l₁ * V₁ P A B μ (Kmat Kuu Kuv Kvu Kvv) z t
                  - l₂ * ((gam P (Kmat Kuu Kuv Kvu Kvv) z) 1 t 0 ^ 2 + (gam P (Kmat Kuu Kuv Kvu Kvv) z) 0 t 1 ^ 2)
                  + C₁ * V₁ P A B μ (Kmat Kuu Kuv Kvu Kvv) z t ^ ((3:ℝ) / 2)
                  + C₂ * supNorm (xderiv (slice (gam P (Kmat Kuu Kuv Kvu Kvv) z) t))
                      * V₁ P A B μ (Kmat Kuu Kuv Kvu Kvv) z t
                  + C₃ * (a t ^ 2 + b t ^ 2) := by sorry

end HyperbolicBackstepping.Quasilinear
