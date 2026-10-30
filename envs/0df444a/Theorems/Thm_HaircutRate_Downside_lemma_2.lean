-- Prove2me | Theorems.Thm_HaircutRate_Downside_lemma_2
-- name    : HaircutRate.Downside.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:57:27.342204+00:00
-- url     : https://prove2.me/theorems/97c643a8-0153-4436-ade2-b1c41418f406
-- title:
--   Lemma 2, p. 18 — E is decreasing, p is increasing, and H is decreasing in the face value
-- statement:
--   Throughout, $\Omega=[\underline\omega,\bar\omega]$ with $0<\underline\omega<\bar\omega$, $K>0$ units of the risky asset paying $\omega$ in state $\omega$, depositors' endowments $0\le e^d_1<e^d_0$, and a utility $u$ of class $C^2$ on $(0,\infty)$ with $u'>0$ and $u''<0$ there. The payoff density $f$ is nonnegative and integrable on $\Omega$ with total mass $1$, $F(x)=\int_{\underline\omega}^{x} f$, and $\mathbb E[\varphi]=\int_{\underline\omega}^{\bar\omega}\varphi f$. Write $D=(e^d_0-e^d_1)/K$ and $q^{bp}(x)=\mathbb E\big[\tfrac{u'(e^d_1+K\min(\omega,x))}{u'(e^d_1+Kx)}\min(\omega,x)\big]$ for the bond pricing curve (23).
--
--   As functions of the face value $x\in\Omega$ at a fixed density, the equity component $E(x)=\mathbb E[\max(\omega-x,0)]$ is decreasing, the asset price $p(x)=q^{bp}(x)+E(x)$ of (28) is increasing, and the haircut $H(x)=E(x)/p(x)$ of (31) is decreasing:
--   $$x\le y\ \Longrightarrow\ E(x)\ge E(y),\quad p(x)\le p(y),\quad \frac{E(x)}{p(x)}\ge\frac{E(y)}{p(y)}.$$
--
--   Lemma 2 is the "indirect effect" in Proposition 2: a lower face value pushes the haircut up.
--
--   **Formalization Note.** "Increasing"/"decreasing" are read as non-strict: (B.4) is strictly positive only where $F(x)>0$.
-- source:
--   Hao, The joint determination of haircuts and interest rates for collateralized loans in shadow banking, author's version of 19 Feb 2025 (sha256 924ec4ed…), Lemma 2, p. 18; proof B.3, p. 36

import Mathlib
import Definitions.Def_HaircutRate_Downside_Setting

namespace HaircutRate.Downside
open Set Economy

theorem lemma_2 (E : Economy) (hE : E.Valid) (f : ℝ → ℝ) (hf : E.IsDensity f) :
    AntitoneOn (E.equity f) (Icc E.lo E.hi) ∧
      MonotoneOn (fun x => E.qbp f x + E.equity f x) (Icc E.lo E.hi) ∧
      AntitoneOn (fun x => E.equity f x / (E.qbp f x + E.equity f x)) (Icc E.lo E.hi) := by sorry

end HaircutRate.Downside
