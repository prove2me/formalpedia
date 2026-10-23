-- Prove2me | Theorems.Thm_HaircutRate_Downside_marginal_value_strictMono
-- name    : HaircutRate.Downside.marginal_value_strictMono
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:57:25.562768+00:00
-- url     : https://prove2.me/theorems/b90577e4-9f65-407c-80f4-d09e1a03a8f3
-- title:
--   Proof of Proposition 2, p. 36 — under Assumption 3, u′(e^d_1 + c)c and u′(e^d_1 + Kω)ω are strictly increasing
-- statement:
--   Let $0<\underline\omega<\bar\omega$, $K>0$, $0\le e^d_1<e^d_0$, and let $u$ be $C^2$ on $(0,\infty)$ with $u'>0$, $u''<0$ there. Assume Assumption 3, $-u''(e^d_1+c)c/u'(e^d_1+c)<1$ for $c\in[K\underline\omega,K\bar\omega]$. Then
--   $$c\mapsto u'(e^d_1+c)\,c\ \text{ is strictly increasing on }[K\underline\omega,K\bar\omega],\qquad \omega\mapsto u'(e^d_1+K\omega)\,\omega\ \text{ is strictly increasing on }[\underline\omega,\bar\omega].$$
--
--   This is what turns a first-order stochastic dominance improvement on the downside into a higher bond price (footnote 26).
--
--   **Formalization Note.** The paper states the second claim over $(\underline\omega,\omega^*)$, a sub-interval of $\Omega$; it is posed on all of $\Omega$, which is the stronger form.
-- source:
--   Hao, The joint determination of haircuts and interest rates for collateralized loans in shadow banking, author's version of 19 Feb 2025 (sha256 924ec4ed…), proof of Proposition 2 (B.6), first two sentences, p. 36; Assumption 3 (32) and footnote 22, p. 18

import Mathlib
import Definitions.Def_HaircutRate_Downside_Setting

namespace HaircutRate.Downside
open Set Economy

theorem marginal_value_strictMono (E : Economy) (hE : E.Valid) (hA3 : E.Assumption3) :
    StrictMonoOn (fun c => deriv E.u (E.e1 + c) * c) (Icc (E.K * E.lo) (E.K * E.hi)) ∧
      StrictMonoOn (fun ω => deriv E.u (E.e1 + E.K * ω) * ω) (Icc E.lo E.hi) := by sorry

end HaircutRate.Downside
