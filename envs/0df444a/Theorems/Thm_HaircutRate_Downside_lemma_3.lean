-- Prove2me | Theorems.Thm_HaircutRate_Downside_lemma_3
-- name    : HaircutRate.Downside.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:57:23.414999+00:00
-- url     : https://prove2.me/theorems/870eb8b6-6fe4-416f-ae19-830d543aace0
-- title:
--   Lemma 3, p. 19 — under Assumption 3, the interest rate R = ω*/q − 1 is increasing in the face value
-- statement:
--   Throughout, $\Omega=[\underline\omega,\bar\omega]$ with $0<\underline\omega<\bar\omega$, $K>0$ units of the risky asset paying $\omega$ in state $\omega$, depositors' endowments $0\le e^d_1<e^d_0$, and a utility $u$ of class $C^2$ on $(0,\infty)$ with $u'>0$ and $u''<0$ there. The payoff density $f$ is nonnegative and integrable on $\Omega$ with total mass $1$, $F(x)=\int_{\underline\omega}^{x} f$, and $\mathbb E[\varphi]=\int_{\underline\omega}^{\bar\omega}\varphi f$. Write $D=(e^d_0-e^d_1)/K$ and $q^{bp}(x)=\mathbb E\big[\tfrac{u'(e^d_1+K\min(\omega,x))}{u'(e^d_1+Kx)}\min(\omega,x)\big]$ for the bond pricing curve (23).
--
--   Assume Assumption 3 (32). Then the quoted interest rate (30), as a function of the face value at a fixed density,
--   $$R(x)=\frac{x}{q^{bp}(x)}-1,$$
--   is increasing on $\Omega$.
--
--   Combined with a lower face value, this gives the interest-rate clause of Proposition 2.
--
--   **Formalization Note.** "Increasing" is read as non-decreasing: (B.5) is strictly negative only where $F(x)>0$.
-- source:
--   Hao, The joint determination of haircuts and interest rates for collateralized loans in shadow banking, author's version of 19 Feb 2025 (sha256 924ec4ed…), Lemma 3, p. 19; proof B.4, p. 36

import Mathlib
import Definitions.Def_HaircutRate_Downside_Setting

namespace HaircutRate.Downside
open Set Economy

theorem lemma_3 (E : Economy) (hE : E.Valid) (hA3 : E.Assumption3) (f : ℝ → ℝ)
    (hf : E.IsDensity f) :
    MonotoneOn (fun x => x / E.qbp f x - 1) (Icc E.lo E.hi) := by sorry

end HaircutRate.Downside
