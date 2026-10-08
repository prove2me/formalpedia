-- Prove2me | Theorems.Thm_NonuniformKuramoto_CondII_gamma_analysis
-- name    : NonuniformKuramoto.CondII.gamma_analysis
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:25:32.206196+00:00
-- url     : https://prove2.me/theorems/470e37d2-7f8d-44d7-98de-b0e69a60ce3b
-- title:
--   Proof of Theorem V.5, p. 26 — (41) on Λ is equivalent to (33); the unique ρ_max ∈ ]π/2−φ_max, π] and γ_min ∈ [0, π/2−φ_max[
-- statement:
--   Let $0\le\varphi_{\max}<\pi/2$, write $a=\pi/2-\varphi_{\max}$, and let $\lambda_c\ge0$ and $\lambda_2>0$ be real numbers (in the application, $\lambda_{\mathrm{critical}}$ and $\lambda_2(L(P_{ij}\cos\varphi_{ij}))$). Put
--   $$
--   f(\rho,\gamma)=\frac{\gamma\operatorname{sinc}(\rho)}{\cos(\varphi_{\max})}-\frac{\lambda_c}{\lambda_2},\qquad \Lambda=\{(\rho,\gamma):\rho\in\,]0,\pi[,\ \gamma\in\,]0,a],\ \gamma<\rho\}.
--   $$
--   1. There is $(\rho,\gamma)\in\Lambda$ satisfying (41), $\lambda_2>\lambda_c\cos(\varphi_{\max})/(\gamma\operatorname{sinc}(\rho))$, if and only if $\lambda_2>\lambda_c$, which is (33).
--   2. If $\lambda_2>\lambda_c$, there is exactly one $\rho_{\max}\in\,]a,\pi]$ with $f(\rho_{\max},a)=0$, and exactly one $\gamma_{\min}\in[0,a[$ with $f(\gamma_{\min},\gamma_{\min})=0$.
--
--   Since $a\operatorname{sinc}(a)=\sin(a)=\cos(\varphi_{\max})$, these are exactly the equations $\operatorname{sinc}(\gamma_{\max})/\operatorname{sinc}(\pi/2-\varphi_{\max})=\sin(\gamma_{\min})/\cos(\varphi_{\max})=\lambda_c/\lambda_2$ of Theorem V.5 (with $\gamma_{\max}=\rho_{\max}$), so this result shows that the radii $\gamma_{\max}$ and $\gamma_{\min}$ of Theorem V.5 exist and are unique.
-- source:
--   Dörfler & Bullo, Synchronization and Transient Stability in Power Networks and Nonuniform Kuramoto Oscillators, arXiv:0910.5673v4, p. 26, Proof of Theorem V.5, analysis of (41)

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondII_Graph
import Definitions.Def_NonuniformKuramoto_CondII_Model
import Definitions.Def_NonuniformKuramoto_CondII_Constants
open Matrix

namespace NonuniformKuramoto.CondII

/-- Proof of Theorem V.5 (Dörfler–Bullo, arXiv:0910.5673v4, p. 26), final analysis of (41).
Write `a = π/2 − ϕ_max`, `λ_c ≥ 0` for `λ_critical`, `λ₂ > 0` for `λ₂(L(P_ij cos ϕ_ij))` and
`f(ρ, γ) = γ sinc(ρ)/cos(ϕ_max) − λ_c/λ₂`. Then (41), `λ₂ > λ_c cos(ϕ_max)/(γ sinc ρ)`, holds
at some `(ρ, γ) ∈ Λ = {ρ ∈ ]0, π[, γ ∈ ]0, a], γ < ρ}` iff (33) `λ₂ > λ_c` holds; and under (33)
there is a unique `ρ_max ∈ ]a, π]` with `f(ρ_max, a) = 0` and a unique `γ_min ∈ [0, a[` with
`f(γ_min, γ_min) = 0`. -/
theorem gamma_analysis (ϕmax lc l2 : ℝ) (hϕ0 : 0 ≤ ϕmax) (hϕ1 : ϕmax < Real.pi / 2)
    (hlc : 0 ≤ lc) (hl2 : 0 < l2) :
    ((∃ ρ γ : ℝ, 0 < ρ ∧ ρ < Real.pi ∧ 0 < γ ∧ γ ≤ Real.pi / 2 - ϕmax ∧ γ < ρ ∧
        lc * Real.cos ϕmax / (γ * Real.sinc ρ) < l2) ↔ lc < l2) ∧
    (lc < l2 →
      (∃! ρmax : ℝ, ρmax ∈ Set.Ioc (Real.pi / 2 - ϕmax) Real.pi ∧
        (Real.pi / 2 - ϕmax) * Real.sinc ρmax / Real.cos ϕmax - lc / l2 = 0) ∧
      (∃! γmin : ℝ, γmin ∈ Set.Ico 0 (Real.pi / 2 - ϕmax) ∧
        γmin * Real.sinc γmin / Real.cos ϕmax - lc / l2 = 0)) := by sorry

end NonuniformKuramoto.CondII
