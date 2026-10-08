-- Prove2me | Theorems.Thm_NonuniformKuramoto_CondII_Xtilde_bound
-- name    : NonuniformKuramoto.CondII.Xtilde_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:24:46.139414+00:00
-- url     : https://prove2.me/theorems/9bf74c9c-e8eb-4866-b099-5a91ba8b3b2a
-- title:
--   Proof of Theorem V.5, p. 25 — ‖HX‖₂ ≤ X̃ (the page prints both inequalities reversed)
-- statement:
--   Under the standing assumptions of §V.B ($D_i>0$, $P_{ij}\ge0$ and $\varphi_{ij}\in[0,\pi/2[$ for $i\ne j$, $P_{ii}=\varphi_{ii}=0$, …), let $X\in\mathbb R^n$ be the lossy coupling vector of (31), $X_i=\sum_{j=1}^n(P_{ij}/D_i)\sin(\varphi_{ij})\cos(\theta_i-\theta_j)$. Then for every configuration $\theta$,
--   $$
--   \|HX\|_2\ \le\ \tilde X:=\sqrt n\,\Big\|\Big[\dots,\sum_j\frac{P_{ij}}{D_i}\sin(\varphi_{ij}),\dots\Big]\Big\|_2 .
--   $$
--
--   The bound removes the state dependence of the lossy coupling from the Lyapunov derivative, leaving a constant that enters $\lambda_{\mathrm{critical}}$.
--
--   **Formalization Note** The page writes this chain as "$\|HX\|_2=\sqrt{X^TH^THX}\ge\sqrt{\lambda_{\max}(H^TH)}\|X\|_2\ge\sqrt n\|[\dots]\|_2=:\tilde X$" and calls $\tilde X$ a lower bound, but the proof uses it as an upper bound in (37), and only the upper bound holds ($\lambda_{\max}(H^TH)=n$ and $|X_i|\le\sum_j(P_{ij}/D_i)\sin\varphi_{ij}$). For $n=2$, $D\equiv1$, $P_{12}=1$, $\varphi_{12}=\varphi_{21}=\pi/4$ and $\theta_1-\theta_2=\pi/2$ one has $X=0$ while $\tilde X=\sqrt2\cdot\sqrt{1/2+1/2}=\sqrt2>0$. The corrected direction is stated.
-- source:
--   Dörfler & Bullo, Synchronization and Transient Stability in Power Networks and Nonuniform Kuramoto Oscillators, arXiv:0910.5673v4, p. 25, Proof of Theorem V.5, display defining X̃; p. 23, (31) for X

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondII_Graph
import Definitions.Def_NonuniformKuramoto_CondII_Model
import Definitions.Def_NonuniformKuramoto_CondII_Constants
open Matrix

namespace NonuniformKuramoto.CondII

/-- Proof of Theorem V.5 (Dörfler–Bullo, arXiv:0910.5673v4, p. 25), corrected: the lossy
coupling vector `X` of (31) satisfies `‖HX‖₂ ≤ X̃ = √n ‖[…, ∑_j (P_ij/D_i) sin(ϕ_ij), …]‖₂`.
The page prints both inequalities of this chain as `≥`; the proof uses `X̃` as an upper bound. -/
theorem Xtilde_bound {n : ℕ} (D : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ)
    (hyp : StandingHyp D P ϕ) (θ : Fin n → ℝ) :
    normH (lossyX D P ϕ θ) ≤ Xtilde D P ϕ := by sorry

end NonuniformKuramoto.CondII
