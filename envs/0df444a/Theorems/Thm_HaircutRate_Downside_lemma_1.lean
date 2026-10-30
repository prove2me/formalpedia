-- Prove2me | Theorems.Thm_HaircutRate_Downside_lemma_1
-- name    : HaircutRate.Downside.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:57:17.17915+00:00
-- url     : https://prove2.me/theorems/46eb5552-b77e-4ff0-98f1-e3bc25154130
-- title:
--   Lemma 1, p. 15 — the bond pricing curve q^{bp}(ω*) is strictly increasing
-- statement:
--   Throughout, $\Omega=[\underline\omega,\bar\omega]$ with $0<\underline\omega<\bar\omega$, $K>0$ units of the risky asset paying $\omega$ in state $\omega$, depositors' endowments $0\le e^d_1<e^d_0$, and a utility $u$ of class $C^2$ on $(0,\infty)$ with $u'>0$ and $u''<0$ there. The payoff density $f$ is nonnegative and integrable on $\Omega$ with total mass $1$, $F(x)=\int_{\underline\omega}^{x} f$, and $\mathbb E[\varphi]=\int_{\underline\omega}^{\bar\omega}\varphi f$. Write $D=(e^d_0-e^d_1)/K$ and $q^{bp}(x)=\mathbb E\big[\tfrac{u'(e^d_1+K\min(\omega,x))}{u'(e^d_1+Kx)}\min(\omega,x)\big]$ for the bond pricing curve (23).
--
--   The bond pricing curve is strictly increasing on $\Omega$:
--   $$\underline\omega\le x<y\le\bar\omega\ \Longrightarrow\ q^{bp}(x)<q^{bp}(y).$$
--
--   Together with (29), this is what makes the equilibrium face value unique and drives every comparative static of the paper.
-- source:
--   Hao, The joint determination of haircuts and interest rates for collateralized loans in shadow banking, author's version of 19 Feb 2025 (sha256 924ec4ed…), Lemma 1, p. 15

import Mathlib
import Definitions.Def_HaircutRate_Downside_Setting

namespace HaircutRate.Downside
open Set Economy

theorem lemma_1 (E : Economy) (hE : E.Valid) (f : ℝ → ℝ) (hf : E.IsDensity f) :
    StrictMonoOn (E.qbp f) (Icc E.lo E.hi) := by sorry

end HaircutRate.Downside
