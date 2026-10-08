-- Prove2me | Theorems.Thm_NonuniformKuramoto_CondII_theorem_V_5
-- name    : NonuniformKuramoto.CondII.theorem_V_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:24:53.201596+00:00
-- url     : https://prove2.me/theorems/f6ac7a95-66de-46b7-8dee-e50940042082
-- title:
--   Theorem V.5 (Synchronization condition II) — λ₂(L(P_ij cos φ_ij)) > λ_critical gives phase cohesiveness in ‖Hθ‖₂ and exponential frequency synchronization
-- statement:
--   Consider the non-uniform Kuramoto model $D_i\dot\theta_i=\omega_i-\sum_{j=1}^nP_{ij}\sin(\theta_i-\theta_j+\varphi_{ij})$ with $n\ge2$ oscillators, $D_i>0$, $P=P^T$ with $P_{ij}\ge0$ inducing a connected graph, $\varphi_{ij}=\varphi_{ji}\in[0,\pi/2[$ for $i\ne j$ and $P_{ii}=\varphi_{ii}=0$. Let $H$ be the incidence matrix of the complete graph, $\kappa=\sum_kD_k$ and $\alpha=\sqrt{\min_{i\ne j}\{D_iD_j\}/\max_{i\ne j}\{D_iD_j\}}$, and assume
--   $$
--   \lambda_2(L(P_{ij}\cos(\varphi_{ij})))>\lambda_{\mathrm{critical}}:=\frac{\|HD^{-1}\omega\|_2+\sqrt n\,\big\|\big[\sum_{j}\frac{P_{1j}}{D_1}\sin(\varphi_{1j}),\dots,\sum_{j}\frac{P_{nj}}{D_n}\sin(\varphi_{nj})\big]\big\|_2}{\cos(\varphi_{\max})(\kappa/n)\alpha/\max_{i\ne j}\{D_iD_j\}}.\tag{33}
--   $$
--   Let $\gamma_{\max}\in\,]\pi/2-\varphi_{\max},\pi]$ and $\gamma_{\min}\in[0,\pi/2-\varphi_{\max}[$ be the solutions of
--   $$
--   \frac{\operatorname{sinc}(\gamma_{\max})}{\operatorname{sinc}(\pi/2-\varphi_{\max})}=\frac{\sin(\gamma_{\min})}{\cos(\varphi_{\max})}=\frac{\lambda_{\mathrm{critical}}}{\lambda_2(L(P_{ij}\cos(\varphi_{ij})))}.
--   $$
--   Then:
--
--   1. **Phase cohesiveness.** For every $\gamma\in[\gamma_{\min},\alpha\gamma_{\max}]$ the set $\{\theta\in\Delta(\pi):\|H\theta\|_2\le\gamma\}$ is positively invariant; and every solution with $\theta(0)\in\Delta(\pi)$ and $\|H\theta(0)\|_2<\alpha\gamma_{\max}$ satisfies, for every $\gamma>\gamma_{\min}$, $\|H\theta(t)\|_2\le\gamma$ for all sufficiently large $t$.
--   2. **Frequency synchronization.** For every such solution the frequencies $\dot\theta_i(t)$ converge exponentially fast to a common $\dot\theta_\infty\in[\dot\theta_{\min}(0),\dot\theta_{\max}(0)]$. If moreover $\varphi_{ij}=0$ for all $i,j$, then $\dot\theta_\infty=\Omega=\sum_i\omega_i/\sum_iD_i$ and, for every $\gamma\in\,]\gamma_{\min},\pi/2[$, $\|\dot\theta(t)-\Omega\mathbf 1\|_2\le Ce^{-\lambda_{\mathrm{fe}}(\gamma)t}$ for some $C$ and all $t\ge0$, where $\lambda_{\mathrm{fe}}(\gamma)=\lambda_2(L(P_{ij}))\cos(\gamma)\cos(\angle(D\mathbf 1,\mathbf 1))^2/D_{\max}$ is the rate of (19).
--
--   Condition (33) asks the algebraic connectivity of the lossless coupling to dominate the non-uniformity of the natural frequencies and the lossy coupling; it is the second of the paper's sufficient conditions for synchronization of non-uniform Kuramoto oscillators and, through them, for transient stability of the network-reduced power system.
--
--   **Formalization Note**
--   1. Configurations are real lifts; $\Delta(\pi)$ means all differences $\theta_i-\theta_j$ are $<\pi$, and $\|H\theta\|_2^2=\sum_{i<j}(\theta_i-\theta_j)^2$ (the page's double sum on p. 23 counts each pair twice; the pair sum agrees with $H\in\mathbb R^{n(n-1)/2\times n}$ and (34)).
--   2. $\varphi_{ij}=\varphi_{ji}$ is added: without it $L(P_{ij}\cos\varphi_{ij})$ is not a symmetric Laplacian. It holds for power networks.
--   3. $\gamma_{\min},\gamma_{\max}$ are universally quantified subject to their defining equations; the milestone `gamma_analysis` shows they exist and are unique.
--   4. The page says each trajectory "reaches $\{\|H\theta\|_2\le\gamma_{\min}\}$". That is false in finite time: for $n=2$, $D\equiv1$, $\varphi\equiv0$, $P_{12}=1$, $\omega=(1,0)$, $x=\theta_1-\theta_2$ solves $\dot x=1-2\sin x$ and tends to $\gamma_{\min}=\pi/6$ from $x(0)=\pi/2$ without reaching it. The statement asserts the asymptotic version: eventually below every $\gamma>\gamma_{\min}$.
--   5. The rate statement of the "Moreover" sentence refers to $\lambda_{\mathrm{fe}}$ of (19), which depends on an arc length $\gamma$ the theorem does not name; it is stated for every $\gamma\in\,]\gamma_{\min},\pi/2[$, which the trajectory eventually satisfies, with (19)'s rate taken positive (the page prints a minus sign).
--   6. The page's "Moreover" sentence begins "if $\gamma_{\max}=0$", a misprint for $\varphi_{\max}=0$ (Theorem V.1 2), which it invokes, has $\varphi_{\max}=0$; $\gamma_{\max}>\pi/2-\varphi_{\max}>0$ can never vanish). With $\varphi_{ij}\ge0$ and $\varphi_{ii}=0$, $\varphi_{\max}=0$ is the hypothesis $\varphi_{ij}=0$ for all $i,j$ used here.
-- source:
--   Dörfler & Bullo, Synchronization and Transient Stability in Power Networks and Nonuniform Kuramoto Oscillators, arXiv:0910.5673v4, pp. 23–24, Theorem V.5, (33); p. 16, Theorem V.1 and (19) for Ω and λ_fe

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondII_Graph
import Definitions.Def_NonuniformKuramoto_CondII_Model
import Definitions.Def_NonuniformKuramoto_CondII_Constants
open Matrix

namespace NonuniformKuramoto.CondII

/-- Theorem V.5 (Synchronization condition II) (Dörfler–Bullo, arXiv:0910.5673v4, pp. 23–24).
Under the standing assumptions of §V.B and condition (33), `λ₂(L(P_ij cos ϕ_ij)) > λ_critical`,
with `γ_max ∈ ]π/2 − ϕ_max, π]` and `γ_min ∈ [0, π/2 − ϕ_max[` the solutions of
`sinc(γ_max)/sinc(π/2 − ϕ_max) = sin(γ_min)/cos(ϕ_max) = λ_critical/λ₂(L(P_ij cos ϕ_ij))`:
1) `{θ ∈ ∆(π) : ‖Hθ‖₂ ≤ γ}` is positively invariant for every `γ ∈ [γ_min, αγ_max]`, and every
   trajectory with `θ(0) ∈ ∆(π)`, `‖Hθ(0)‖₂ < αγ_max` ends up in `{‖Hθ‖₂ ≤ γ}` for every
   `γ > γ_min` (the page says "reaches `{‖Hθ‖₂ ≤ γ_min}`", which holds only asymptotically);
2) for such trajectories the frequencies synchronize exponentially to some
   `θ̇_∞ ∈ [θ̇_min(0), θ̇_max(0)]`; if `ϕ ≡ 0`, then `θ̇_∞ = Ω` and the rate is no worse than
   `λ_fe(γ)` of (19) for every `γ ∈ ]γ_min, π/2[`. -/
theorem theorem_V_5 {n : ℕ} (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ)
    (hyp : StandingHyp D P ϕ)
    (hcrit : lambdaCritical D ω P ϕ < lambda2 (lossless P ϕ))
    (γmin γmax : ℝ)
    (hγmin : γmin ∈ Set.Ico 0 (Real.pi / 2 - phiMax ϕ) ∧
      Real.sin γmin / Real.cos (phiMax ϕ) = lambdaCritical D ω P ϕ / lambda2 (lossless P ϕ))
    (hγmax : γmax ∈ Set.Ioc (Real.pi / 2 - phiMax ϕ) Real.pi ∧
      Real.sinc γmax / Real.sinc (Real.pi / 2 - phiMax ϕ) =
        lambdaCritical D ω P ϕ / lambda2 (lossless P ϕ)) :
    -- 1) phase cohesiveness: positive invariance
    (∀ γ ∈ Set.Icc γmin (alpha D * γmax),
      IsPositivelyInvariant D ω P ϕ (fun θ => NonuniformKuramoto.CondI.ArcOpen Real.pi θ ∧ normH θ ≤ γ)) ∧
    -- 1) phase cohesiveness: ultimate bound (corrected: asymptotic)
    (∀ θ : ℝ → Fin n → ℝ, NonuniformKuramoto.CondI.IsSolution D ω P ϕ θ → NonuniformKuramoto.CondI.ArcOpen Real.pi (θ 0) →
      normH (θ 0) < alpha D * γmax →
      ∀ γ, γmin < γ → ∃ T : ℝ, 0 ≤ T ∧ ∀ t, T ≤ t → normH (θ t) ≤ γ) ∧
    -- 2) frequency synchronization
    (∀ θ : ℝ → Fin n → ℝ, NonuniformKuramoto.CondI.IsSolution D ω P ϕ θ → NonuniformKuramoto.CondI.ArcOpen Real.pi (θ 0) →
      normH (θ 0) < alpha D * γmax →
      ∃ ωinf : ℝ,
        (∃ C r : ℝ, 0 < r ∧ ∀ t, 0 ≤ t → ∀ i,
          |NonuniformKuramoto.CondI.field D ω P ϕ (θ t) i - ωinf| ≤ C * Real.exp (-r * t)) ∧
        (∃ i, NonuniformKuramoto.CondI.field D ω P ϕ (θ 0) i ≤ ωinf) ∧ (∃ i, ωinf ≤ NonuniformKuramoto.CondI.field D ω P ϕ (θ 0) i) ∧
        ((∀ i j, ϕ i j = 0) →
          ωinf = NonuniformKuramoto.CondI.Omega D ω ∧
          ∀ γ, γmin < γ → γ < Real.pi / 2 → ∃ C : ℝ, ∀ t, 0 ≤ t →
            euclNorm (fun i => NonuniformKuramoto.CondI.field D ω P ϕ (θ t) i - NonuniformKuramoto.CondI.Omega D ω) ≤
              C * Real.exp (-lambdaFe D P γ * t))) := by sorry

end NonuniformKuramoto.CondII
