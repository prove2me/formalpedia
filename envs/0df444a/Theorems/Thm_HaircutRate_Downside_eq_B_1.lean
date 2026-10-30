-- Prove2me | Theorems.Thm_HaircutRate_Downside_eq_B_1
-- name    : HaircutRate.Downside.eq_B_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:57:16.087889+00:00
-- url     : https://prove2.me/theorems/56b25b9a-30c8-423c-8a06-076a1769e1b6
-- title:
--   (B.1), proof of Lemma 1, p. 35 — derivative of the bond pricing curve at an interior face value, and its positivity
-- statement:
--   Throughout, $\Omega=[\underline\omega,\bar\omega]$ with $0<\underline\omega<\bar\omega$, $K>0$ units of the risky asset paying $\omega$ in state $\omega$, depositors' endowments $0\le e^d_1<e^d_0$, and a utility $u$ of class $C^2$ on $(0,\infty)$ with $u'>0$ and $u''<0$ there. The payoff density $f$ is nonnegative and integrable on $\Omega$ with total mass $1$, $F(x)=\int_{\underline\omega}^{x} f$, and $\mathbb E[\varphi]=\int_{\underline\omega}^{\bar\omega}\varphi f$. Write $D=(e^d_0-e^d_1)/K$ and $q^{bp}(x)=\mathbb E\big[\tfrac{u'(e^d_1+K\min(\omega,x))}{u'(e^d_1+Kx)}\min(\omega,x)\big]$ for the bond pricing curve (23).
--
--   For every interior face value $x\in(\underline\omega,\bar\omega)$ the bond pricing curve is differentiable at $x$ with
--   $$\frac{\partial q^{bp}(x)}{\partial x}=\int_{\underline\omega}^{x}\frac{-u'(e^d_1+K\omega)\,u''(e^d_1+Kx)}{(u'(e^d_1+Kx))^2}\,K\omega\,dF(\omega)+1-F(x)>0 .$$
--
--   This is the computation behind Lemma 1 and the slope $\partial q/\partial\omega^*$ that enters (34) and (35).
--
--   **Formalization Note.** Only interior points are claimed, where a two-sided derivative makes sense. The density $f$ is only assumed integrable; the integrand $\min(\omega,x)$ has a kink at $\omega=x$ but is Lipschitz in $x$.
-- source:
--   Hao, The joint determination of haircuts and interest rates for collateralized loans in shadow banking, author's version of 19 Feb 2025 (sha256 924ec4ed…), (B.1), proof of Lemma 1, p. 35

import Mathlib
import Definitions.Def_HaircutRate_Downside_Setting

namespace HaircutRate.Downside
open Set Economy

theorem eq_B_1 (E : Economy) (hE : E.Valid) (f : ℝ → ℝ) (hf : E.IsDensity f) :
    ∀ x ∈ Ioo E.lo E.hi, HasDerivAt (E.qbp f) (E.dqbp f x) x ∧ 0 < E.dqbp f x := by sorry

end HaircutRate.Downside
