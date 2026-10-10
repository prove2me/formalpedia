-- Prove2me | Theorems.Thm_NonconvexDRS_Tight_eq_4_13
-- name    : NonconvexDRS.Tight.eq_4_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:55.681409+00:00
-- url     : https://prove2.me/theorems/f0429495-4ba7-4cff-b9fc-fb223a18445d
-- title:
--   (4.13), p. 16 — prox_{γφ₁} is well defined iff γ < 1/[σ]₋, its closed form, and prox_{γδ_{±1}} = sgn
-- statement:
--   Let $L>0$, $\sigma\in[-L,L]$, $t>1$ and $\gamma>0$, let $\varphi_1$ be the function (4.12) and $\varphi_2=\delta_{\{\pm1\}}$. Write $[\sigma]_-=\max\{0,-\sigma\}$, with the convention $1/0=\infty$. Then:
--
--   1. $\operatorname{prox}_{\gamma\varphi_1}$ is well defined — for every $s\in\mathbb R$ it consists of exactly one point — if and only if $\gamma<1/[\sigma]_-$;
--   2. in that case, for every $s\in\mathbb R$,
--   $$\operatorname{prox}_{\gamma\varphi_1}(s)=\begin{cases}\dfrac{s}{1+\gamma L} & \text{if } s\le t(1+\gamma L),\\[1ex] \dfrac{s-\gamma(L-\sigma)t}{1+\gamma\sigma} & \text{otherwise;}\end{cases}$$
--   3. $\operatorname{prox}_{\gamma\varphi_2}=\operatorname{sgn}$, where $\operatorname{sgn}(0)=\{\pm1\}$.
--
--   Verbatim (p. 16): "Moreover, $\operatorname{prox}_{\gamma\varphi_1}$ is well defined iff $\gamma<1/[\sigma]_-$, in which case [the display (4.13)] where $\operatorname{sgn}(0)=\{\pm1\}$."
--
--   These closed forms let one follow the DRS iterates of the counterexample explicitly.
--
--   **Formalization Note** "Well defined" is read as "single-valued with nonempty values at every $s$". The bound $\gamma<1/[\sigma]_-$ is written $\gamma[\sigma]_-<1$, so that $[\sigma]_-=0$ imposes no constraint.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, p. 16, proof of Theorem 4.7, (4.13)

import Mathlib
import Definitions.Def_NonconvexDRS_Tight_Setting
open Filter Topology

namespace NonconvexDRS.Tight

theorem eq_4_13 (L σ t γ : ℝ) (hL : 0 < L) (hσ : -L ≤ σ ∧ σ ≤ L) (ht : 1 < t) (hγ : 0 < γ) :
    ((∀ s : ℝ, ∃! u : ℝ, u ∈ proxSet (fun x => (phi1Ex L σ t x : EReal)) γ s) ↔
      γ * NonconvexDRS.DRS.negPartR σ < 1) ∧
    (γ * NonconvexDRS.DRS.negPartR σ < 1 → ∀ s : ℝ,
      proxSet (fun x => (phi1Ex L σ t x : EReal)) γ s =
        {if s ≤ t * (1 + γ * L) then s / (1 + γ * L)
          else (s - γ * (L - σ) * t) / (1 + γ * σ)}) ∧
    (∀ x : ℝ, proxSet (indic ({-1, 1} : Set ℝ)) γ x = sgnSet x) := by sorry

end NonconvexDRS.Tight
