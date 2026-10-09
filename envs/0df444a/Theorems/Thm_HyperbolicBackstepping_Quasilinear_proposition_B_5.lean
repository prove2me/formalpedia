-- Prove2me | Theorems.Thm_HyperbolicBackstepping_Quasilinear_proposition_B_5
-- name    : HyperbolicBackstepping.Quasilinear.proposition_B_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:23:55.077971+00:00
-- url     : https://prove2.me/theorems/0805e1a4-15cc-4688-b1ed-c1d118ebe409
-- title:
--   Proposition B.5, p. 27 — for ‖γ‖_∞ + ‖η‖_∞ small, the norms of θ = γ_tt and γ_xx are comparable
-- statement:
--   Under the standing hypotheses of §2 with $q\ne0$, a $C^2$ full kernel solving (3.30)–(3.37), and $d_1,d_2>0$, $d_1\ne d_2$, there are $\delta>0$ and positive constants $c_1,c_2,c_3,c_4$ such that for every classical solution $(z,a,b)$ of the closed loop, with $\gamma=\mathcal K[\Phi z]$, $\eta=\gamma_t$, $\theta=\gamma_{tt}$, and every $t\ge0$ with $\|\gamma(\cdot,t)\|_\infty+\|\eta(\cdot,t)\|_\infty<\delta$:
--   1. $\|\theta\|_\infty\le c_1(\|\gamma_{xx}\|_\infty+\|\gamma_x\|_\infty+\|\gamma\|_\infty)$;
--   2. $\|\theta\|_{L^2}\le c_2(\|\gamma_{xx}\|_{L^2}+\|\gamma_x\|_{L^2}+\|\gamma\|_{L^2})$;
--   3. $\|\gamma_{xx}\|_\infty\le c_3(\|\theta\|_\infty+\|\eta\|_\infty+\|\gamma\|_\infty)$;
--   4. $\|\gamma_{xx}\|_{L^2}\le c_4(\|\theta\|_{L^2}+\|\eta\|_{L^2}+\|\gamma\|_{L^2})$.
--
--   With Lemma B.6 this shows that $V_1+V_2+V_3$ is equivalent to $\|\gamma\|_{H^2}^2$ for small states, the last step of the proof of Theorem 4.1.
--
--   **Formalization Note** Solutions are classical ($C^2$), which is enough for $\theta$ and $\gamma_{xx}$ to be continuous. Constants are chosen after the data and before the solution.
-- source:
--   Coron, Vazquez, Krstic and Bastin, Local Exponential H² Stabilization of a 2 × 2 Quasilinear Hyperbolic System Using Backstepping, arXiv:1208.6475v1, p. 27, Proposition B.5, (B.27)–(B.30)

import Mathlib
import Definitions.Def_HyperbolicBackstepping_Quasilinear_ClosedLoop
import Definitions.Def_HyperbolicBackstepping_Quasilinear_Backstepping

namespace HyperbolicBackstepping.Quasilinear

theorem proposition_B_5 (P : Plant) (hq : P.q ≠ 0)
    (Kuu Kuv Kvu Kvv : ℝ → ℝ → ℝ)
    (hK : IsFullKernel P.ε₁ P.ε₂ P.c₁ P.c₂ P.q Kuu Kuv Kvu Kvv)
    (d₁ d₂ : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd : d₁ ≠ d₂) :
    ∃ δ : ℝ, 0 < δ ∧
      ∃ c₁ c₂ c₃ c₄ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧ 0 < c₄ ∧
        ∀ (z : ℝ → ℝ → Fin 2 → ℝ) (a b : ℝ → ℝ),
          IsClosedLoopSolution P Kvu Kvv d₁ d₂ z a b →
          ∀ t : ℝ, 0 ≤ t →
            supNorm (slice (gam P (Kmat Kuu Kuv Kvu Kvv) z) t) + supNorm (slice (eta P (Kmat Kuu Kuv Kvu Kvv) z) t) < δ →
            supNorm (slice (theta P (Kmat Kuu Kuv Kvu Kvv) z) t)
                ≤ c₁ * (supNorm (xderiv (xderiv (slice (gam P (Kmat Kuu Kuv Kvu Kvv) z) t)))
                  + supNorm (xderiv (slice (gam P (Kmat Kuu Kuv Kvu Kvv) z) t)) + supNorm (slice (gam P (Kmat Kuu Kuv Kvu Kvv) z) t)) ∧
            HyperbolicBackstepping.Linear.L2norm (slice (theta P (Kmat Kuu Kuv Kvu Kvv) z) t)
                ≤ c₂ * (HyperbolicBackstepping.Linear.L2norm (xderiv (xderiv (slice (gam P (Kmat Kuu Kuv Kvu Kvv) z) t)))
                  + HyperbolicBackstepping.Linear.L2norm (xderiv (slice (gam P (Kmat Kuu Kuv Kvu Kvv) z) t)) + HyperbolicBackstepping.Linear.L2norm (slice (gam P (Kmat Kuu Kuv Kvu Kvv) z) t)) ∧
            supNorm (xderiv (xderiv (slice (gam P (Kmat Kuu Kuv Kvu Kvv) z) t)))
                ≤ c₃ * (supNorm (slice (theta P (Kmat Kuu Kuv Kvu Kvv) z) t) + supNorm (slice (eta P (Kmat Kuu Kuv Kvu Kvv) z) t)
                  + supNorm (slice (gam P (Kmat Kuu Kuv Kvu Kvv) z) t)) ∧
            HyperbolicBackstepping.Linear.L2norm (xderiv (xderiv (slice (gam P (Kmat Kuu Kuv Kvu Kvv) z) t)))
                ≤ c₄ * (HyperbolicBackstepping.Linear.L2norm (slice (theta P (Kmat Kuu Kuv Kvu Kvv) z) t) + HyperbolicBackstepping.Linear.L2norm (slice (eta P (Kmat Kuu Kuv Kvu Kvv) z) t)
                  + HyperbolicBackstepping.Linear.L2norm (slice (gam P (Kmat Kuu Kuv Kvu Kvv) z) t)) := by sorry

end HyperbolicBackstepping.Quasilinear
