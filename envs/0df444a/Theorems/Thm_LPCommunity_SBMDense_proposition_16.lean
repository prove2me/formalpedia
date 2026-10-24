-- Prove2me | Theorems.Thm_LPCommunity_SBMDense_proposition_16
-- name    : LPCommunity.SBMDense.proposition_16
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T12:38:19.193887+00:00
-- url     : https://prove2.me/theorems/1444536b-5532-4dd8-b02f-54391885024d
-- title:
--   Proposition 16, p. 29 — in the very dense SBM, $(1-\epsilon)(2-(p+q)/2)\le\rho_{\mathrm{avg}}\le\rho_{\max}=2$ w.h.p.
-- statement:
--   Let $0<q<p<1$ be constants and let $G\sim\mathcal G_{n,p,q}$. Then for every $\epsilon>0$,
--
--   $$
--   \lim_{n\to\infty}\mathbb P\Big[(1-\epsilon)\Big(2-\frac{p+q}{2}\Big)\le\rho_{\mathrm{avg}}(G)\le\rho_{\max}(G)=2\Big]=1.
--   $$
--
--   This is the distance input of Condition 1 of Theorem 7 (display (28)).
--
--   **Formalization Note** $n=2m$ runs over the even numbers. $\rho_{\max}$ is in `ℕ∞` and $\rho_{\mathrm{avg}}$ in $[0,\infty]$; the middle inequality compares them in $[0,\infty]$ and is part of the event, as printed. The lower endpoint is embedded with `ENNReal.ofReal`.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 29, Proposition 16

import Mathlib
import Definitions.Def_LPCommunity_LPFail_Setting
import Definitions.Def_LPCommunity_SBMDense_RandomGraphs

open scoped ENNReal

namespace LPCommunity.SBMDense

theorem proposition_16 (p q : ℝ) (hq : 0 < q) (hqp : q < p) (hp : p < 1) (ε : ℝ) (hε : 0 < ε) :
    Filter.Tendsto
      (fun m : ℕ => LPCommunity.SBMRecovery.sbmProb (2 * m) p q
        (fun _ G => ENNReal.ofReal ((1 - ε) * (2 - (p + q) / 2)) ≤ LPCommunity.LPFail.rhoAvg G ∧
          LPCommunity.LPFail.rhoAvg G ≤ ((LPCommunity.LPFail.rhoMax G : ℕ∞) : ℝ≥0∞) ∧ LPCommunity.LPFail.rhoMax G = 2))
      Filter.atTop (nhds 1) := by sorry

end LPCommunity.SBMDense
