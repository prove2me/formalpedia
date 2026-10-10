-- Prove2me | Theorems.Thm_NonconvexDRS_Tight_residual_cases
-- name    : NonconvexDRS.Tight.residual_cases
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:59.02764+00:00
-- url     : https://prove2.me/theorems/db66c328-815a-4bda-b1a7-95ca63c8466c
-- title:
--   Proof of Theorem 4.7, p. 16 — for γ > 1/L, vᵏ = −sgn(sᵏ) when sᵏ ≤ t(1+γL), and the two forms of uᵏ − vᵏ
-- statement:
--   Let $L>0$, $\sigma\in[-L,L]$, $t>1$, and let $\gamma$ satisfy $1/L<\gamma<1/[\sigma]_-$; let $\lambda>0$. Let $\varphi_1$ be (4.12) and $\varphi_2=\delta_{\{\pm1\}}$, and let $(s^k,u^k,v^k)_{k\in\mathbb N}$ be any DRS run with stepsize $\gamma$ and relaxation $\lambda$. Then for every $k\in\mathbb N$,
--   $$u^k-v^k\in\begin{cases}\dfrac{s^k}{1+\gamma L}+\operatorname{sgn}(s^k) & \text{if } s^k\le t(1+\gamma L),\\[1ex] \dfrac{s^k}{1+\gamma\sigma}-\dfrac{\gamma(L-\sigma)t}{1+\gamma\sigma}-v^k & \text{otherwise,}\end{cases}$$
--   where $v^k\in\{1,-1\}$ in the second case.
--
--   Verbatim (p. 16): "For any $k\in\mathbb N$ we have $v^k=-\operatorname{sgn}(s^k)$ if $s^k\le t(1+\gamma L)$, resulting in [the display], where $v^k$ is either $1$ or $-1$ in the second case."
--
--   This is the case analysis from which the paper concludes that $\|u^k-v^k\|$, hence the residual $\|s^k-s^{k+1}\|=\lambda\|u^k-v^k\|$, stays bounded away from zero.
--
--   **Formalization Note** The page takes $1/L\le\gamma$; here $\gamma>1/L$ (written $1<\gamma L$). At $\gamma=1/L$ the first case fails: for $s^k\le t(1+\gamma L)$ one has $2u^k-s^k=0$, so $v^k$ may be either sign. For instance, with $s^k=2$, $u^k=v^k=1$, $L=1$, $\sigma=0$, $t=2$, $\gamma=1$, $u^k-v^k=0\notin 1+\operatorname{sgn}(2)$. The bound $\gamma<1/[\sigma]_-$ is written $\gamma[\sigma]_-<1$.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, p. 16, proof of Theorem 4.7, the display after (4.13)

import Mathlib
import Definitions.Def_NonconvexDRS_Tight_Setting
open Filter Topology

namespace NonconvexDRS.Tight

theorem residual_cases (L σ t γ lam : ℝ) (hL : 0 < L) (hσ : -L ≤ σ ∧ σ ≤ L) (ht : 1 < t)
    (hγL : 1 < γ * L) (hγσ : γ * NonconvexDRS.DRS.negPartR σ < 1) (hlam : 0 < lam)
    (s u v : ℕ → ℝ) (hrun : IsDRSRun (phi1Ex L σ t) (indic ({-1, 1} : Set ℝ)) γ lam s u v)
    (k : ℕ) :
    (s k ≤ t * (1 + γ * L) →
      u k - v k ∈ {y : ℝ | ∃ w ∈ sgnSet (s k), y = s k / (1 + γ * L) + w}) ∧
    (t * (1 + γ * L) < s k →
      (v k = 1 ∨ v k = -1) ∧
        u k - v k = s k / (1 + γ * σ) - γ * (L - σ) * t / (1 + γ * σ) - v k) := by sorry

end NonconvexDRS.Tight
