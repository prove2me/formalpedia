-- Prove2me | Theorems.Thm_HyperbolicBackstepping_Quasilinear_proposition_5_3
-- name    : HyperbolicBackstepping.Quasilinear.proposition_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:23:03.902592+00:00
-- url     : https://prove2.me/theorems/6fcc8eac-23bc-4140-99bf-01005e47f70d
-- title:
--   Proposition 5.3, p. 16 — for ‖γ‖_∞ small, V₂ = ∫ηᵀR[γ]η satisfies the differential inequality (5.55)
-- statement:
--   Under the standing hypotheses of §2 with $q\ne0$, a $C^2$ full kernel solving (3.30)–(3.37), and $d_1,d_2>0$, $d_1\ne d_2$, there are a weight $D$ of the form (3.9) (constants $A,B,\mu>0$), $\delta_2>0$ and positive constants $\lambda_3,\lambda_4,K_1,K_2$ such that the following holds. For every classical solution $(z,a,b)$ of the closed loop, let $\gamma=\mathcal K[\Phi z]$, $\eta=\gamma_t=(\eta_1,\eta_2)$, $R[\gamma]=D+\begin{pmatrix}0&\psi\\\psi&0\end{pmatrix}$ with $\psi$ of (5.42), and $V_2(t)=\int_0^1\eta^{\mathsf T}R[\gamma]\eta\,dx$. Then for every $t\ge0$ with $\|\gamma(\cdot,t)\|_\infty<\delta_2$,
--   $$\dot V_2\le-\lambda_3V_2-\lambda_4\big(\eta_1^2(1,t)+\eta_2^2(0,t)\big)+K_1V_2\|\eta\|_\infty+K_2\big(a(t)^2+b(t)^2\big).$$
--
--   This is the $H^1$-level Lyapunov estimate of the proof of Theorem 4.1.
--
--   **Formalization Note** The page prints the last term as $K_2b(t)^2$. The proof derives it from the boundary term $K_3(1+\|\gamma\|_\infty)(a^2+b^2)$ of (5.51), and the boundary value $\eta_2(1,t)=-\varphi_2(1)(d_1a+d_2b)$ is nonzero when $b=0\ne a$, so Lean states $K_2(a^2+b^2)$, the bound the proof supports. The printed "for $\lambda_2,\lambda_3,K_1,K_2$" names $\lambda_3,\lambda_4,K_1,K_2$. The paper uses the same $D$ as in $V_1$; Lean asserts that some $D$ of the form (3.9) works. $R$ is given by its construction (5.40)–(5.42) (Lemma 5.2). Constants come after the data and before the solution.
-- source:
--   Coron, Vazquez, Krstic and Bastin, Local Exponential H² Stabilization of a 2 × 2 Quasilinear Hyperbolic System Using Backstepping, arXiv:1208.6475v1, p. 16, Proposition 5.3, (5.55); V₂ (5.48) p. 15; R[γ] (5.40)–(5.42) p. 14

import Mathlib
import Definitions.Def_HyperbolicBackstepping_Quasilinear_ClosedLoop
import Definitions.Def_HyperbolicBackstepping_Quasilinear_Backstepping

namespace HyperbolicBackstepping.Quasilinear

theorem proposition_5_3 (P : Plant) (hq : P.q ≠ 0)
    (Kuu Kuv Kvu Kvv : ℝ → ℝ → ℝ)
    (hK : IsFullKernel P.ε₁ P.ε₂ P.c₁ P.c₂ P.q Kuu Kuv Kvu Kvv)
    (d₁ d₂ : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd : d₁ ≠ d₂) :
    ∃ A B μ : ℝ, 0 < A ∧ 0 < B ∧ 0 < μ ∧
      ∃ δ₂ : ℝ, 0 < δ₂ ∧
        ∃ l₃ l₄ K₁ K₂ : ℝ, 0 < l₃ ∧ 0 < l₄ ∧ 0 < K₁ ∧ 0 < K₂ ∧
          ∀ (z : ℝ → ℝ → Fin 2 → ℝ) (a b : ℝ → ℝ),
            IsClosedLoopSolution P Kvu Kvv d₁ d₂ z a b →
            ∀ t : ℝ, 0 ≤ t →
              supNorm (slice (gam P (Kmat Kuu Kuv Kvu Kvv) z) t) < δ₂ →
              deriv (fun s => V₂ P A B μ (Kmat Kuu Kuv Kvu Kvv) z s) t
                ≤ -l₃ * V₂ P A B μ (Kmat Kuu Kuv Kvu Kvv) z t
                  - l₄ * ((eta P (Kmat Kuu Kuv Kvu Kvv) z) 1 t 0 ^ 2 + (eta P (Kmat Kuu Kuv Kvu Kvv) z) 0 t 1 ^ 2)
                  + K₁ * V₂ P A B μ (Kmat Kuu Kuv Kvu Kvv) z t * supNorm (slice (eta P (Kmat Kuu Kuv Kvu Kvv) z) t)
                  + K₂ * (a t ^ 2 + b t ^ 2) := by sorry

end HyperbolicBackstepping.Quasilinear
