-- Prove2me | Theorems.Thm_HaircutRate_Downside_theorem_1_eq_29
-- name    : HaircutRate.Downside.theorem_1_eq_29
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:57:17.875979+00:00
-- url     : https://prove2.me/theorems/463d6a35-6780-4702-bb46-c81bfe382d4b
-- title:
--   Theorem 1, (29), p. 17, with proof B.2, p. 35 — under Assumption 2, (29) has a unique root ω* ∈ Ω, and ω* ∈ (ω̲, ω̄)
-- statement:
--   Throughout, $\Omega=[\underline\omega,\bar\omega]$ with $0<\underline\omega<\bar\omega$, $K>0$ units of the risky asset paying $\omega$ in state $\omega$, depositors' endowments $0\le e^d_1<e^d_0$, and a utility $u$ of class $C^2$ on $(0,\infty)$ with $u'>0$ and $u''<0$ there. The payoff density $f$ is nonnegative and integrable on $\Omega$ with total mass $1$, $F(x)=\int_{\underline\omega}^{x} f$, and $\mathbb E[\varphi]=\int_{\underline\omega}^{\bar\omega}\varphi f$. Write $D=(e^d_0-e^d_1)/K$ and $q^{bp}(x)=\mathbb E\big[\tfrac{u'(e^d_1+K\min(\omega,x))}{u'(e^d_1+Kx)}\min(\omega,x)\big]$ for the bond pricing curve (23).
--
--   Assume Assumption 2: $2\underline\omega<D$ (20) and $\bar\omega+\mathbb E\big[\tfrac{u'(e^d_1+K\omega)}{u'(e^d_1+K\bar\omega)}\omega\big]>D$ (21). Then the equilibrium condition
--   $$\omega^*+q^{bp}(\omega^*)=\frac{e^d_0-e^d_1}{K}\qquad(29)$$
--   has exactly one solution $\omega^*\in[\underline\omega,\bar\omega]$; the mission's face value $\omega^*$ is that solution, and it lies in the open interval $(\underline\omega,\bar\omega)$.
--
--   This is the part of Theorem 1 that the comparative statics of §3 use: the face value of the traded bond is well defined.
--
--   **Formalization Note.** Only the first paragraph of the proof of Theorem 1 (B.2) is stated; the existence and uniqueness of the competitive equilibrium of Definition 1 is not formalized.
-- source:
--   Hao, The joint determination of haircuts and interest rates for collateralized loans in shadow banking, author's version of 19 Feb 2025 (sha256 924ec4ed…), Theorem 1, (29), p. 17; proof of Theorem 1 (B.2), first sentence, p. 35

import Mathlib
import Definitions.Def_HaircutRate_Downside_Setting

namespace HaircutRate.Downside
open Set Economy

theorem theorem_1_eq_29 (E : Economy) (hE : E.Valid) (f : ℝ → ℝ) (hf : E.IsDensity f)
    (hA2 : E.Assumption2 f) :
    (∃! x, E.IsFaceValue f x) ∧ E.IsFaceValue f (E.faceValue f) ∧
      E.faceValue f ∈ Ioo E.lo E.hi := by sorry

end HaircutRate.Downside
