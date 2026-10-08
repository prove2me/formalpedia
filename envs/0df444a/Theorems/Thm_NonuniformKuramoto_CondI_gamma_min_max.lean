-- Prove2me | Theorems.Thm_NonuniformKuramoto_CondI_gamma_min_max
-- name    : NonuniformKuramoto.CondI.gamma_min_max
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:24:46.646666+00:00
-- url     : https://prove2.me/theorems/5bd9a162-958c-43fd-9c55-4e7aea2cad40
-- title:
--   Proof of Theorem V.3, p. 22 — (30) holds iff $\gamma\in[\gamma_{\min},\gamma_{\max}]$; $\gamma_{\min},\gamma_{\max}$ are the unique solutions in their ranges
-- statement:
--   Consider the non-uniform Kuramoto model (8) with $n\ge2$, $D_i>0$, $P_{ij}>0$ and $\varphi_{ij}\in[0,\pi/2[$ for $i\ne j$, $P_{ii}=\varphi_{ii}=0$, and assume condition (26), $\Gamma_{\min}>\Gamma_{\mathrm{critical}}$. Let $c=\cos(\varphi_{\max})\Gamma_{\mathrm{critical}}/\Gamma_{\min}$, $\gamma_{\min}=\arcsin c$ and $\gamma_{\max}=\pi-\arcsin c$. Then
--
--   1. $\gamma_{\min}\in[0,\pi/2-\varphi_{\max}[$ and $\gamma_{\max}\in\,]\pi/2,\pi]$;
--   2. $\sin(\gamma_{\min})=\sin(\gamma_{\max})=c$;
--   3. $\gamma_{\min}$ is the only $\gamma\in[0,\pi/2-\varphi_{\max}[$ with $\sin\gamma=c$, and $\gamma_{\max}$ the only $\gamma\in\,]\pi/2,\pi]$ with $\sin\gamma=c$;
--   4. for every $\gamma\in[0,\pi]$,
--   $$\Gamma_{\min}\sin(\gamma)\ge\cos(\varphi_{\max})\,\Gamma_{\mathrm{critical}}\qquad(30)$$
--   holds if and only if $\gamma\in[\gamma_{\min},\gamma_{\max}]$.
--
--   This identifies the arc lengths for which the arc containing all phases cannot grow, and certifies that the explicit formulas for $\gamma_{\min},\gamma_{\max}$ are the "unique solutions" named in Theorem V.3.
-- source:
--   Dörfler & Bullo, Synchronization and Transient Stability in Power Networks and Nonuniform Kuramoto Oscillators, arXiv:0910.5673v4, p. 22, proof of Theorem V.3, (30) and the following sentences; p. 20, definition of γ_min, γ_max

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondI_Model
import Definitions.Def_NonuniformKuramoto_CondI_Constants

namespace NonuniformKuramoto.CondI

/-- Proof of Theorem V.3, p. 22, (30): under (26), `γ_min = arcsin c` and `γ_max = π − arcsin c`,
`c = cos(ϕ_max) Γ_critical / Γ_min`, lie in `[0, π/2 − ϕ_max[` and `]π/2, π]`, are the unique solutions
of `sin γ = c` there, and for `γ ∈ [0, π]` inequality (30) `Γ_min sin γ ≥ cos(ϕ_max) Γ_critical`
holds exactly when `γ ∈ [γ_min, γ_max]`. -/
theorem gamma_min_max {n : ℕ} (hn : 2 ≤ n) (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ)
    (hD : ∀ i, 0 < D i)
    (hP : ∀ i j, i ≠ j → 0 < P i j) (hPii : ∀ i, P i i = 0) (hϕii : ∀ i, ϕ i i = 0)
    (hϕ : ∀ i j, i ≠ j → 0 ≤ ϕ i j ∧ ϕ i j < Real.pi / 2)
    (h26 : GammaCrit D ω P ϕ < GammaMin D P ϕ) :
    gammaMin D ω P ϕ ∈ Set.Ico 0 (Real.pi / 2 - phiMax ϕ) ∧
    gammaMax D ω P ϕ ∈ Set.Ioc (Real.pi / 2) Real.pi ∧
    Real.sin (gammaMin D ω P ϕ) = Real.cos (phiMax ϕ) * GammaCrit D ω P ϕ / GammaMin D P ϕ ∧
    Real.sin (gammaMax D ω P ϕ) = Real.cos (phiMax ϕ) * GammaCrit D ω P ϕ / GammaMin D P ϕ ∧
    (∀ γ ∈ Set.Ico 0 (Real.pi / 2 - phiMax ϕ),
      Real.sin γ = Real.cos (phiMax ϕ) * GammaCrit D ω P ϕ / GammaMin D P ϕ →
        γ = gammaMin D ω P ϕ) ∧
    (∀ γ ∈ Set.Ioc (Real.pi / 2) Real.pi,
      Real.sin γ = Real.cos (phiMax ϕ) * GammaCrit D ω P ϕ / GammaMin D P ϕ →
        γ = gammaMax D ω P ϕ) ∧
    (∀ γ ∈ Set.Icc 0 Real.pi,
      (Real.cos (phiMax ϕ) * GammaCrit D ω P ϕ ≤ GammaMin D P ϕ * Real.sin γ ↔
        γ ∈ Set.Icc (gammaMin D ω P ϕ) (gammaMax D ω P ϕ))) := by sorry

end NonuniformKuramoto.CondI
