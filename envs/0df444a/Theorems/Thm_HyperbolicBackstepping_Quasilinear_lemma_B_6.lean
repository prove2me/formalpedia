-- Prove2me | Theorems.Thm_HyperbolicBackstepping_Quasilinear_lemma_B_6
-- name    : HyperbolicBackstepping.Quasilinear.lemma_B_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:22:35.924486+00:00
-- url     : https://prove2.me/theorems/f6ad1e5e-a3cf-4511-89b3-0e888c7e1d02
-- title:
--   Lemma B.6, p. 27 — for ‖γ‖_∞ small, the sup and L² norms of η = γ_t and γ_x are comparable
-- statement:
--   Under the standing hypotheses of §2 with $q\ne0$, a $C^2$ full kernel solving (3.30)–(3.37), and $d_1,d_2>0$, $d_1\ne d_2$, there are $\delta_2>0$ and positive constants $c_1,c_2,c_3,c_4$ such that for every classical solution $(z,a,b)$ of the closed loop, with $\gamma=\mathcal K[\Phi z]$ and $\eta=\gamma_t$, and every $t\ge0$ with $\|\gamma(\cdot,t)\|_\infty<\delta_2$:
--   1. $\|\eta\|_\infty\le c_1(\|\gamma_x\|_\infty+\|\gamma\|_\infty)$;
--   2. $\|\eta\|_{L^2}\le c_2(\|\gamma_x\|_{L^2}+\|\gamma\|_{L^2})$;
--   3. $\|\gamma_x\|_\infty\le c_3(\|\eta\|_\infty+\|\gamma\|_\infty)$;
--   4. $\|\gamma_x\|_{L^2}\le c_4(\|\eta\|_{L^2}+\|\gamma\|_{L^2})$,
--
--   all norms taken at time $t$ over $x\in[0,1]$, with $|\gamma|=|\alpha|+|\beta|$ in the sup norm.
--
--   The lemma lets the proof trade spatial derivatives of $\gamma$ for time derivatives, which are what the Lyapunov functional $V_2$ controls.
--
--   **Formalization Note** The relation between $\eta$ and $\gamma_x$ is the transformed equation (5.15); in Lean it is implicit in the hypothesis that $\gamma$ comes from a classical closed-loop solution. Constants are chosen after the data and before the solution.
-- source:
--   Coron, Vazquez, Krstic and Bastin, Local Exponential H² Stabilization of a 2 × 2 Quasilinear Hyperbolic System Using Backstepping, arXiv:1208.6475v1, p. 27, Lemma B.6, (B.31)–(B.34)

import Mathlib
import Definitions.Def_HyperbolicBackstepping_Quasilinear_ClosedLoop
import Definitions.Def_HyperbolicBackstepping_Quasilinear_Backstepping

namespace HyperbolicBackstepping.Quasilinear

theorem lemma_B_6 (P : Plant) (hq : P.q ≠ 0)
    (Kuu Kuv Kvu Kvv : ℝ → ℝ → ℝ)
    (hK : IsFullKernel P.ε₁ P.ε₂ P.c₁ P.c₂ P.q Kuu Kuv Kvu Kvv)
    (d₁ d₂ : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd : d₁ ≠ d₂) :
    ∃ δ₂ : ℝ, 0 < δ₂ ∧
      ∃ c₁ c₂ c₃ c₄ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧ 0 < c₄ ∧
        ∀ (z : ℝ → ℝ → Fin 2 → ℝ) (a b : ℝ → ℝ),
          IsClosedLoopSolution P Kvu Kvv d₁ d₂ z a b →
          ∀ t : ℝ, 0 ≤ t →
            supNorm (slice (gam P (Kmat Kuu Kuv Kvu Kvv) z) t) < δ₂ →
            supNorm (slice (eta P (Kmat Kuu Kuv Kvu Kvv) z) t)
                ≤ c₁ * (supNorm (xderiv (slice (gam P (Kmat Kuu Kuv Kvu Kvv) z) t)) + supNorm (slice (gam P (Kmat Kuu Kuv Kvu Kvv) z) t)) ∧
            HyperbolicBackstepping.Linear.L2norm (slice (eta P (Kmat Kuu Kuv Kvu Kvv) z) t)
                ≤ c₂ * (HyperbolicBackstepping.Linear.L2norm (xderiv (slice (gam P (Kmat Kuu Kuv Kvu Kvv) z) t)) + HyperbolicBackstepping.Linear.L2norm (slice (gam P (Kmat Kuu Kuv Kvu Kvv) z) t)) ∧
            supNorm (xderiv (slice (gam P (Kmat Kuu Kuv Kvu Kvv) z) t))
                ≤ c₃ * (supNorm (slice (eta P (Kmat Kuu Kuv Kvu Kvv) z) t) + supNorm (slice (gam P (Kmat Kuu Kuv Kvu Kvv) z) t)) ∧
            HyperbolicBackstepping.Linear.L2norm (xderiv (slice (gam P (Kmat Kuu Kuv Kvu Kvv) z) t))
                ≤ c₄ * (HyperbolicBackstepping.Linear.L2norm (slice (eta P (Kmat Kuu Kuv Kvu Kvv) z) t) + HyperbolicBackstepping.Linear.L2norm (slice (gam P (Kmat Kuu Kuv Kvu Kvv) z) t)) := by sorry

end HyperbolicBackstepping.Quasilinear
