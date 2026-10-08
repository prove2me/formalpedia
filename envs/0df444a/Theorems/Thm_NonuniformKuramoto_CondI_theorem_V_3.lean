-- Prove2me | Theorems.Thm_NonuniformKuramoto_CondI_theorem_V_3
-- name    : NonuniformKuramoto.CondI.theorem_V_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:24:38.129789+00:00
-- url     : https://prove2.me/theorems/d3b52a40-40c3-4b36-ac0d-998751ed8768
-- title:
--   Theorem V.3 (Synchronization condition I), corrected — $\Gamma_{\min}>\Gamma_{\mathrm{critical}}$ gives phase cohesiveness and exponential frequency synchronization
-- statement:
--   Consider the non-uniform Kuramoto model (8),
--
--   $$D_i\dot\theta_i=\omega_i-\sum_{j=1}^nP_{ij}\sin(\theta_i-\theta_j+\varphi_{ij}),$$
--
--   with $n\ge2$ oscillators, $D_i>0$, $\omega_i\in\mathbb R$, a symmetric complete coupling graph ($P_{ij}=P_{ji}>0$ for $i\ne j$), phase shifts $\varphi_{ij}\in[0,\pi/2[$ for $i\ne j$, and $P_{ii}=\varphi_{ii}=0$. Assume that the minimal lossless coupling of any oscillator to the network exceeds a critical value:
--
--   $$\Gamma_{\min}:=n\min_{i\neq j}\Big\{\frac{P_{ij}}{D_i}\cos(\varphi_{ij})\Big\}>\Gamma_{\mathrm{critical}}:=\frac{1}{\cos(\varphi_{\max})}\Big(\max_{i\neq j}\Big|\frac{\omega_i}{D_i}-\frac{\omega_j}{D_j}\Big|+2\max_{i}\sum_{j=1}^n\frac{P_{ij}}{D_i}\sin(\varphi_{ij})\Big).\qquad(26)$$
--
--   Let $\gamma_{\min}\in[0,\pi/2-\varphi_{\max}[$ and $\gamma_{\max}\in\,]\pi/2,\pi]$ be the solutions of $\sin(\gamma_{\min})=\sin(\gamma_{\max})=\cos(\varphi_{\max})\Gamma_{\mathrm{critical}}/\Gamma_{\min}$. Then:
--
--   1. **Phase cohesiveness.** $\bar\Delta(\gamma)$ is positively invariant for every $\gamma\in[\gamma_{\min},\gamma_{\max}]$; and every solution with $\theta(0)\in\Delta(\gamma_{\max})$ satisfies, for every $\gamma\in\,]\gamma_{\min},\gamma_{\max}]$, $\theta(t)\in\bar\Delta(\gamma)$ for all $t$ beyond some $T\ge0$.
--   2. **Frequency synchronization.** For every solution with $\theta(0)\in\Delta(\gamma_{\max})$ there are $\dot\theta_\infty$, $C$ and $\lambda>0$ with $|\dot\theta_i(t)-\dot\theta_\infty|\le Ce^{-\lambda t}$ for all $t\ge0$ and all $i$; if moreover $\theta(0)\in\Delta(\pi/2-\varphi_{\max})$, then $\dot\theta_\infty\in[\dot\theta_{\min}(0),\dot\theta_{\max}(0)]$.
--
--   This is the paper's main synchronization result for the non-uniform Kuramoto model (statements 1)–2) of Theorem III.2): an explicit algebraic test on the network parameters that guarantees phase cohesiveness and frequency synchronization, and hence transient stability of the associated power network.
--
--   **Formalization Note** Two clauses of the printed theorem are false as stated and are replaced by their corrected forms. (i) "Each trajectory starting in $\Delta(\gamma_{\max})$ reaches $\bar\Delta(\gamma_{\min})$" holds only asymptotically: for $n=2$, $\varphi\equiv0$, $D\equiv1$, $P_{12}=P_{21}=1$, $\omega=(1,0)$ one gets $\gamma_{\min}=\pi/6$, the difference $x=\theta_1-\theta_2$ solves $\dot x=1-2\sin x$, and from $x(0)=\pi/2$ it decreases to the equilibrium $\pi/6$ without reaching it; the corrected clause says that $\bar\Delta(\gamma)$ is reached for every $\gamma>\gamma_{\min}$. (ii) "$\dot\theta_\infty\in[\dot\theta_{\min}(0),\dot\theta_{\max}(0)]$ for every $\theta(0)\in\Delta(\gamma_{\max})$" fails: for $n=2$, $D\equiv1$, $\omega\equiv0$, $P_{12}=P_{21}=1$, $\varphi_{12}=\varphi_{21}=1/2$, condition (26) holds, $\theta(0)=(2.4,0)\in\Delta(\gamma_{\max})$ has $\dot\theta(0)\approx(-0.239,0.946)$ but $\dot\theta_\infty=-\sin\frac12\approx-0.479$. The range bound is stated for $\theta(0)\in\Delta(\pi/2-\varphi_{\max})$, where Theorem V.1 1) gives it; exponential synchronization is stated for every $\theta(0)\in\Delta(\gamma_{\max})$, with one limit $\dot\theta_\infty$ for both parts. Arc sets are stated on real lifts of the phases; $\gamma_{\min}=\arcsin c$, $\gamma_{\max}=\pi-\arcsin c$ with $c=\cos(\varphi_{\max})\Gamma_{\mathrm{critical}}/\Gamma_{\min}$ (the milestone `gamma_min_max` shows these are the unique solutions in the stated ranges); $n\ge2$ and $P_{ii}=\varphi_{ii}=0$ are the page's conventions made explicit.
-- source:
--   Dörfler & Bullo, Synchronization and Transient Stability in Power Networks and Nonuniform Kuramoto Oscillators, arXiv:0910.5673v4, pp. 19–20, Theorem V.3 (= Theorem III.2 1)–2), p. 9; see p. 27); proof pp. 21–22

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondI_Model
import Definitions.Def_NonuniformKuramoto_CondI_Constants

namespace NonuniformKuramoto.CondI

/-- Theorem V.3 (Synchronization condition I), pp. 19–20, with the two printed clauses that are false
as stated replaced by their corrected forms (see the item's Formalization Note):
1) `∆̄(γ)` is positively invariant for every `γ ∈ [γ_min, γ_max]`, and every solution with
   `θ(0) ∈ ∆(γ_max)` enters and stays in `∆̄(γ)` for every `γ ∈ ]γ_min, γ_max]` (asymptotic reading of
   "reaches `∆̄(γ_min)`");
2) every solution with `θ(0) ∈ ∆(γ_max)` achieves exponential frequency synchronization to some
   `θ̇_∞`, and `θ̇_∞ ∈ [θ̇_min(0), θ̇_max(0)]` whenever moreover `θ(0) ∈ ∆(π/2 − ϕ_max)`. -/
theorem theorem_V_3 {n : ℕ} (hn : 2 ≤ n) (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ)
    (hD : ∀ i, 0 < D i) (hPsymm : ∀ i j, P i j = P j i)
    (hP : ∀ i j, i ≠ j → 0 < P i j) (hPii : ∀ i, P i i = 0) (hϕii : ∀ i, ϕ i i = 0)
    (hϕ : ∀ i j, i ≠ j → 0 ≤ ϕ i j ∧ ϕ i j < Real.pi / 2)
    (h26 : GammaCrit D ω P ϕ < GammaMin D P ϕ) :
    (∀ γ ∈ Set.Icc (gammaMin D ω P ϕ) (gammaMax D ω P ϕ),
      IsPosInvariant D ω P ϕ (ArcClosed γ)) ∧
    ∀ θ : ℝ → Fin n → ℝ, IsSolution D ω P ϕ θ → ArcOpen (gammaMax D ω P ϕ) (θ 0) →
      (∀ γ ∈ Set.Ioc (gammaMin D ω P ϕ) (gammaMax D ω P ϕ),
        ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → ArcClosed γ (θ t)) ∧
      ∃ ωinf C r : ℝ, 0 < r ∧
        (∀ t : ℝ, 0 ≤ t → ∀ i, |field D ω P ϕ (θ t) i - ωinf| ≤ C * Real.exp (-r * t)) ∧
        (ArcOpen (Real.pi / 2 - phiMax ϕ) (θ 0) →
          (∃ i, field D ω P ϕ (θ 0) i ≤ ωinf) ∧ (∃ i, ωinf ≤ field D ω P ϕ (θ 0) i)) := by sorry

end NonuniformKuramoto.CondI
