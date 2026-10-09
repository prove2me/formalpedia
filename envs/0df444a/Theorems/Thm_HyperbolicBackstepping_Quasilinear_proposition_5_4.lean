-- Prove2me | Theorems.Thm_HyperbolicBackstepping_Quasilinear_proposition_5_4
-- name    : HyperbolicBackstepping.Quasilinear.proposition_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:22:45.231358+00:00
-- url     : https://prove2.me/theorems/f3e35103-84d3-4554-803f-f2d68f0a540e
-- title:
--   Proposition 5.4, p. 17 — for ‖γ‖_∞ + ‖η‖_∞ small, V₃ = ∫θᵀR[γ]θ satisfies the differential inequality (5.69)
-- statement:
--   Under the standing hypotheses of §2 with $q\ne0$, a $C^2$ full kernel solving (3.30)–(3.37), and $d_1,d_2>0$, $d_1\ne d_2$, there are a weight $D$ of the form (3.9) (constants $A,B,\mu>0$), $\delta_3>0$ and positive constants $\lambda_5,\lambda_6,K_1,\dots,K_5$ such that the following holds. For every classical solution $(z,a,b)$ of the closed loop for which $z$ is moreover of class $C^3$, let $\gamma=\mathcal K[\Phi z]$, $\eta=\gamma_t$, $\theta=\gamma_{tt}=(\theta_1,\theta_2)$, $R[\gamma]=D+\begin{pmatrix}0&\psi\\\psi&0\end{pmatrix}$ with $\psi$ of (5.42),
--   $$V_2(t)=\int_0^1\eta^{\mathsf T}R[\gamma]\eta\,dx,\qquad V_3(t)=\int_0^1\theta^{\mathsf T}R[\gamma]\theta\,dx.$$
--   Then for every $t\ge0$ with $\|\gamma(\cdot,t)\|_\infty+\|\eta(\cdot,t)\|_\infty<\delta_3$,
--   $$\dot V_3\le-\lambda_5V_3-\lambda_6\big(\theta_1^2(1,t)+\theta_2^2(0,t)\big)+K_1V_3V_2^{1/2}+K_2V_2V_3^{1/2}+K_3V_3^{3/2}+K_4\|\eta\|_\infty\eta_2^2(0,t)+K_5\big(a(t)^2+b(t)^2\big).$$
--
--   This is the $H^2$-level Lyapunov estimate of the proof of Theorem 4.1; together with Propositions 5.1 and 5.3 it gives the inequality (5.70) for $W=V_1+V_2+V_3$.
--
--   **Formalization Note** $\dot V_3$ involves $\theta_t=\gamma_{ttt}$, so the statement is made for closed-loop solutions that are $C^3$ in $(x,t)$ (the paper works with $H^2$ solutions and computes $\dot V_3$ formally). The same weight $D$ (constants $A,B,\mu$) is used in $V_2$ and $V_3$, as in the paper; Lean asserts that some $D$ of the form (3.9) works. $R$ is given by its construction (5.40)–(5.42) (Lemma 5.2); for $\|\gamma\|_\infty$ small it is positive definite, so $V_2,V_3\ge0$ and the real powers $V^{1/2}$, $V^{3/2}$ are the usual ones. Indices are 0-based: $\theta_1(1,t)$ is `theta … 1 t 0` and $\eta_2(0,t)$ is `eta … 0 t 1`. Constants come after the data and before the solution.
-- source:
--   Coron, Vazquez, Krstic and Bastin, Local Exponential H² Stabilization of a 2 × 2 Quasilinear Hyperbolic System Using Backstepping, arXiv:1208.6475v1, p. 17, Proposition 5.4, (5.69); V₃ (5.64) p. 16; R[γ] (5.40)–(5.42) p. 14

import Mathlib
import Definitions.Def_HyperbolicBackstepping_Quasilinear_ClosedLoop
import Definitions.Def_HyperbolicBackstepping_Quasilinear_Backstepping

namespace HyperbolicBackstepping.Quasilinear

theorem proposition_5_4 (P : Plant) (hq : P.q ≠ 0)
    (Kuu Kuv Kvu Kvv : ℝ → ℝ → ℝ)
    (hK : IsFullKernel P.ε₁ P.ε₂ P.c₁ P.c₂ P.q Kuu Kuv Kvu Kvv)
    (d₁ d₂ : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd : d₁ ≠ d₂) :
    ∃ A B μ : ℝ, 0 < A ∧ 0 < B ∧ 0 < μ ∧
      ∃ δ₃ : ℝ, 0 < δ₃ ∧
        ∃ l₅ l₆ K₁ K₂ K₃ K₄ K₅ : ℝ, 0 < l₅ ∧ 0 < l₆ ∧ 0 < K₁ ∧ 0 < K₂ ∧ 0 < K₃ ∧ 0 < K₄ ∧ 0 < K₅ ∧
          ∀ (z : ℝ → ℝ → Fin 2 → ℝ) (a b : ℝ → ℝ),
            IsClosedLoopSolution P Kvu Kvv d₁ d₂ z a b →
            ContDiff ℝ 3 (fun p : ℝ × ℝ => z p.1 p.2) →
            ∀ t : ℝ, 0 ≤ t →
              supNorm (slice (gam P (Kmat Kuu Kuv Kvu Kvv) z) t)
                + supNorm (slice (eta P (Kmat Kuu Kuv Kvu Kvv) z) t) < δ₃ →
              deriv (fun s => V₃ P A B μ (Kmat Kuu Kuv Kvu Kvv) z s) t
                ≤ -l₅ * V₃ P A B μ (Kmat Kuu Kuv Kvu Kvv) z t
                  - l₆ * ((theta P (Kmat Kuu Kuv Kvu Kvv) z) 1 t 0 ^ 2 + (theta P (Kmat Kuu Kuv Kvu Kvv) z) 0 t 1 ^ 2)
                  + K₁ * V₃ P A B μ (Kmat Kuu Kuv Kvu Kvv) z t * V₂ P A B μ (Kmat Kuu Kuv Kvu Kvv) z t ^ ((1:ℝ) / 2)
                  + K₂ * V₂ P A B μ (Kmat Kuu Kuv Kvu Kvv) z t * V₃ P A B μ (Kmat Kuu Kuv Kvu Kvv) z t ^ ((1:ℝ) / 2)
                  + K₃ * V₃ P A B μ (Kmat Kuu Kuv Kvu Kvv) z t ^ ((3:ℝ) / 2)
                  + K₄ * supNorm (slice (eta P (Kmat Kuu Kuv Kvu Kvv) z) t)
                      * (eta P (Kmat Kuu Kuv Kvu Kvv) z) 0 t 1 ^ 2
                  + K₅ * (a t ^ 2 + b t ^ 2) := by sorry

end HyperbolicBackstepping.Quasilinear
