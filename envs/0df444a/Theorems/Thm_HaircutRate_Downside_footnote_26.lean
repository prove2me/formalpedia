-- Prove2me | Theorems.Thm_HaircutRate_Downside_footnote_26
-- name    : HaircutRate.Downside.footnote_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:57:20.548425+00:00
-- url     : https://prove2.me/theorems/eb69f1ab-ed06-4d1b-8cba-64a01775c69a
-- title:
--   p. 22 and footnote 26 — the Gateaux derivative ∂q/∂τ of q^{bp}(ω*) in a downside direction ψ is positive
-- statement:
--   Throughout, $\Omega=[\underline\omega,\bar\omega]$ with $0<\underline\omega<\bar\omega$, $K>0$ units of the risky asset paying $\omega$ in state $\omega$, depositors' endowments $0\le e^d_1<e^d_0$, and a utility $u$ of class $C^2$ on $(0,\infty)$ with $u'>0$ and $u''<0$ there. The payoff density $f$ is nonnegative and integrable on $\Omega$ with total mass $1$, $F(x)=\int_{\underline\omega}^{x} f$, and $\mathbb E[\varphi]=\int_{\underline\omega}^{\bar\omega}\varphi f$. Write $D=(e^d_0-e^d_1)/K$ and $q^{bp}(x)=\mathbb E\big[\tfrac{u'(e^d_1+K\min(\omega,x))}{u'(e^d_1+Kx)}\min(\omega,x)\big]$ for the bond pricing curve (23). A downside improvement direction $\psi$ at the pre-shock face value $\omega^*$ is an integrable function vanishing outside $(\underline\omega,\omega^*)$ with $\int_{\underline\omega}^{\omega^*}\psi=0$ and $\int_{\underline\omega}^{\omega^*}v\psi>0$ for every $v$ strictly increasing on $[\underline\omega,\omega^*]$.
--
--   Assume Assumptions 2 and 3, and let $\omega^*$ be the equilibrium face value. Then the bond pricing curve of the shocked density $f+\tau\psi$, evaluated at the pre-shock face value, is differentiable in $\tau$ at $\tau=0$ with
--   $$\frac{\partial q}{\partial\tau}=\int_{\underline\omega}^{\omega^*}\frac{u'(e^d_1+K\omega)}{u'(e^d_1+K\omega^*)}\,\omega\,\psi(\omega)\,d\omega>0 .$$
--
--   This is the direct effect of a better downside: at an unchanged face value, the bond is worth more.
-- source:
--   Hao, The joint determination of haircuts and interest rates for collateralized loans in shadow banking, author's version of 19 Feb 2025 (sha256 924ec4ed…), p. 22 and footnote 26; footnote 23, p. 19

import Mathlib
import Definitions.Def_HaircutRate_Downside_Setting

namespace HaircutRate.Downside
open Set Economy

theorem footnote_26 (E : Economy) (hE : E.Valid) (hA3 : E.Assumption3) (f : ℝ → ℝ)
    (hf : E.IsDensity f) (hA2 : E.Assumption2 f)
    (ψ : ℝ → ℝ) (hψ : E.IsDownsideImprovement (E.faceValue f) ψ) :
    HasDerivAt (fun τ => E.qbp (shock f ψ τ) (E.faceValue f)) (E.dqTau ψ (E.faceValue f)) 0 ∧
      0 < E.dqTau ψ (E.faceValue f) := by sorry

end HaircutRate.Downside
