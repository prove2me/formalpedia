-- Prove2me | Theorems.Thm_HaircutRate_Downside_eq_34
-- name    : HaircutRate.Downside.eq_34
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:57:19.399257+00:00
-- url     : https://prove2.me/theorems/d739f87f-a4e6-4bbf-b926-bc2ff88d2283
-- title:
--   (34), p. 22 — dω*/dτ = −(∂q/∂τ)(1 + ∂q/∂ω*)^{−1} < 0 (right derivative at τ = 0)
-- statement:
--   Throughout, $\Omega=[\underline\omega,\bar\omega]$ with $0<\underline\omega<\bar\omega$, $K>0$ units of the risky asset paying $\omega$ in state $\omega$, depositors' endowments $0\le e^d_1<e^d_0$, and a utility $u$ of class $C^2$ on $(0,\infty)$ with $u'>0$ and $u''<0$ there. The payoff density $f$ is nonnegative and integrable on $\Omega$ with total mass $1$, $F(x)=\int_{\underline\omega}^{x} f$, and $\mathbb E[\varphi]=\int_{\underline\omega}^{\bar\omega}\varphi f$. Write $D=(e^d_0-e^d_1)/K$ and $q^{bp}(x)=\mathbb E\big[\tfrac{u'(e^d_1+K\min(\omega,x))}{u'(e^d_1+Kx)}\min(\omega,x)\big]$ for the bond pricing curve (23). A downside improvement direction $\psi$ at the pre-shock face value $\omega^*$ is an integrable function vanishing outside $(\underline\omega,\omega^*)$ with $\int_{\underline\omega}^{\omega^*}\psi=0$ and $\int_{\underline\omega}^{\omega^*}v\psi>0$ for every $v$ strictly increasing on $[\underline\omega,\omega^*]$; the shocked density is $f+\tau\psi$, and $\tau_0>0$ is such that $f+\tau\psi\ge 0$ on $\Omega$ for all $\tau\in[0,\tau_0]$.
--
--   Assume Assumptions 2 and 3, and let $\omega^*(\tau)$ be the equilibrium face value under $f+\tau\psi$. Then $\tau\mapsto\omega^*(\tau)$ has a right derivative at $\tau=0$ given by
--   $$\frac{d\omega^*}{d\tau}=-\frac{\partial q}{\partial\tau}\Big(1+\frac{\partial q}{\partial\omega^*}\Big)^{-1}<0,$$
--   where $\partial q/\partial\tau$ is the footnote-26 integral and $\partial q/\partial\omega^*$ is the (B.1) expression at the pre-shock $\omega^*$.
--
--   **Formalization Note.** The derivative is one-sided ($\tau\ge0$), the direction in which $f+\tau\psi$ is a density. The value of $\partial q/\partial\omega^*$ is written out as the (B.1) expression, not as a `deriv`.
-- source:
--   Hao, The joint determination of haircuts and interest rates for collateralized loans in shadow banking, author's version of 19 Feb 2025 (sha256 924ec4ed…), (34), p. 22

import Mathlib
import Definitions.Def_HaircutRate_Downside_Setting

namespace HaircutRate.Downside
open Set Economy

theorem eq_34 (E : Economy) (hE : E.Valid) (hA3 : E.Assumption3) (f : ℝ → ℝ)
    (hf : E.IsDensity f) (hA2 : E.Assumption2 f)
    (ψ : ℝ → ℝ) (hψ : E.IsDownsideImprovement (E.faceValue f) ψ)
    (τ₀ : ℝ) (hτ₀ : 0 < τ₀)
    (hdens : ∀ τ ∈ Icc 0 τ₀, ∀ ω ∈ Icc E.lo E.hi, 0 ≤ shock f ψ τ ω) :
    HasDerivWithinAt (fun τ => E.faceValue (shock f ψ τ))
        (-E.dqTau ψ (E.faceValue f) / (1 + E.dqbp f (E.faceValue f))) (Ici 0) 0 ∧
      -E.dqTau ψ (E.faceValue f) / (1 + E.dqbp f (E.faceValue f)) < 0 := by sorry

end HaircutRate.Downside
