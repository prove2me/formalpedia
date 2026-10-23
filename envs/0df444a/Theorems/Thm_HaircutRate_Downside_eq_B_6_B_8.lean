-- Prove2me | Theorems.Thm_HaircutRate_Downside_eq_B_6_B_8
-- name    : HaircutRate.Downside.eq_B_6_B_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:57:21.888988+00:00
-- url     : https://prove2.me/theorems/a4485dc5-58b8-46e3-82ab-22f2f82e2d87
-- title:
--   (B.6)–(B.8), p. 37 — at equilibrium E/q = E[(ω − ω*)⁺]/(D − ω*), and its ω*-derivative has the sign of the (33) margin
-- statement:
--   Throughout, $\Omega=[\underline\omega,\bar\omega]$ with $0<\underline\omega<\bar\omega$, $K>0$ units of the risky asset paying $\omega$ in state $\omega$, depositors' endowments $0\le e^d_1<e^d_0$, and a utility $u$ of class $C^2$ on $(0,\infty)$ with $u'>0$ and $u''<0$ there. The payoff density $f$ is nonnegative and integrable on $\Omega$ with total mass $1$, $F(x)=\int_{\underline\omega}^{x} f$, and $\mathbb E[\varphi]=\int_{\underline\omega}^{\bar\omega}\varphi f$. Write $D=(e^d_0-e^d_1)/K$ and $q^{bp}(x)=\mathbb E\big[\tfrac{u'(e^d_1+K\min(\omega,x))}{u'(e^d_1+Kx)}\min(\omega,x)\big]$ for the bond pricing curve (23).
--
--   Assume Assumption 2 and let $\omega^*$ be the equilibrium face value. Then
--
--   1. at equilibrium the equity–debt ratio is $\dfrac{E}{q}=\dfrac{\mathbb E[\max(\omega-\omega^*,0)]}{D-\omega^*}$ (B.6);
--   2. for every $x\in(\underline\omega,\bar\omega)$ with $x<D$, the function $h(y)=\mathbb E[\max(\omega-y,0)]/(D-y)$ is differentiable at $x$ with
--   $$h'(x)=\frac{-(1-F(x))\,D+\int_{x}^{\bar\omega}\omega\,dF(\omega)}{(D-x)^2}\qquad\text{(B.7)},$$
--   and $h'(x)>0$ if and only if $\int_{x}^{\bar\omega}\omega\,dF(\omega)>(1-F(x))\,D$, i.e. $\mathbb E[\omega\mid\omega>x]>D$ (B.8).
--
--   **Formalization Note.** The page says (B.7) "is positive"; that holds only under (B.8), so the sign is posed as an equivalence. Condition (B.8) is multiplied out by $1-F(x)$, which avoids an undefined conditional expectation when $F(x)=1$.
-- source:
--   Hao, The joint determination of haircuts and interest rates for collateralized loans in shadow banking, author's version of 19 Feb 2025 (sha256 924ec4ed…), (B.6)–(B.8), proof of Proposition 2, p. 37

import Mathlib
import Definitions.Def_HaircutRate_Downside_Setting

namespace HaircutRate.Downside
open Set Economy

theorem eq_B_6_B_8 (E : Economy) (hE : E.Valid) (f : ℝ → ℝ) (hf : E.IsDensity f)
    (hA2 : E.Assumption2 f) :
    E.equity f (E.faceValue f) / E.bondPrice f =
        E.equity f (E.faceValue f) / (E.D - E.faceValue f) ∧
      ∀ x ∈ Ioo E.lo E.hi, x < E.D →
        HasDerivAt (fun y => E.equity f y / (E.D - y)) (E.margin f x / (E.D - x) ^ 2) x ∧
          (0 < E.margin f x / (E.D - x) ^ 2 ↔
            (1 - E.cdf f x) * E.D < ∫ ω in x..E.hi, ω * f ω) := by sorry

end HaircutRate.Downside
