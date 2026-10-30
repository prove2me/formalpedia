-- Prove2me | Theorems.Thm_HaircutRate_Downside_eq_35
-- name    : HaircutRate.Downside.eq_35
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:57:31.177598+00:00
-- url     : https://prove2.me/theorems/41d99622-8e03-49d1-8505-dd5b07727fb7
-- title:
--   (35), p. 22 — d(E/q)/dτ at τ = 0 equals −(∂q/∂τ)/(q²(1 + ∂q/∂ω*)) times the (33) margin
-- statement:
--   Throughout, $\Omega=[\underline\omega,\bar\omega]$ with $0<\underline\omega<\bar\omega$, $K>0$ units of the risky asset paying $\omega$ in state $\omega$, depositors' endowments $0\le e^d_1<e^d_0$, and a utility $u$ of class $C^2$ on $(0,\infty)$ with $u'>0$ and $u''<0$ there. The payoff density $f$ is nonnegative and integrable on $\Omega$ with total mass $1$, $F(x)=\int_{\underline\omega}^{x} f$, and $\mathbb E[\varphi]=\int_{\underline\omega}^{\bar\omega}\varphi f$. Write $D=(e^d_0-e^d_1)/K$ and $q^{bp}(x)=\mathbb E\big[\tfrac{u'(e^d_1+K\min(\omega,x))}{u'(e^d_1+Kx)}\min(\omega,x)\big]$ for the bond pricing curve (23). A downside improvement direction $\psi$ at the pre-shock face value $\omega^*$ is an integrable function vanishing outside $(\underline\omega,\omega^*)$ with $\int_{\underline\omega}^{\omega^*}\psi=0$ and $\int_{\underline\omega}^{\omega^*}v\psi>0$ for every $v$ strictly increasing on $[\underline\omega,\omega^*]$; the shocked density is $f+\tau\psi$, and $\tau_0>0$ is such that $f+\tau\psi\ge 0$ on $\Omega$ for all $\tau\in[0,\tau_0]$.
--
--   Assume Assumptions 2 and 3. Let $E(\tau)$, $q(\tau)$ be the equity component and bond price at the equilibrium of $f+\tau\psi$. Then $\tau\mapsto E(\tau)/q(\tau)$ has a right derivative at $\tau=0$ equal to
--   $$\frac{d(E/q)}{d\tau}=-\frac{\partial q/\partial\tau}{q^2\,(1+\partial q/\partial\omega^*)}\Big(\int_{\omega^*}^{\bar\omega}\omega\,dF(\omega)-(1-F(\omega^*))\frac{e^d_0-e^d_1}{K}\Big),$$
--   with $q$, $\partial q/\partial\tau$ (footnote 26), $\partial q/\partial\omega^*$ (B.1) and $F$ taken before the shock.
--
--   This is the decomposition (35) into a negative direct effect and a positive indirect effect; the paper's "$\propto$" is made explicit by the positive factor $(\partial q/\partial\tau)/(q^2(1+\partial q/\partial\omega^*))$.
-- source:
--   Hao, The joint determination of haircuts and interest rates for collateralized loans in shadow banking, author's version of 19 Feb 2025 (sha256 924ec4ed…), (35), p. 22

import Mathlib
import Definitions.Def_HaircutRate_Downside_Setting

namespace HaircutRate.Downside
open Set Economy

theorem eq_35 (E : Economy) (hE : E.Valid) (hA3 : E.Assumption3) (f : ℝ → ℝ)
    (hf : E.IsDensity f) (hA2 : E.Assumption2 f)
    (ψ : ℝ → ℝ) (hψ : E.IsDownsideImprovement (E.faceValue f) ψ)
    (τ₀ : ℝ) (hτ₀ : 0 < τ₀)
    (hdens : ∀ τ ∈ Icc 0 τ₀, ∀ ω ∈ Icc E.lo E.hi, 0 ≤ shock f ψ τ ω) :
    HasDerivWithinAt
      (fun τ => E.equity (shock f ψ τ) (E.faceValue (shock f ψ τ)) / E.bondPrice (shock f ψ τ))
      (-E.dqTau ψ (E.faceValue f) /
          (E.bondPrice f ^ 2 * (1 + E.dqbp f (E.faceValue f))) * E.margin f (E.faceValue f))
      (Ici 0) 0 := by sorry

end HaircutRate.Downside
