-- Prove2me | Theorems.Thm_LeaderStyle_WageFloor_cost_FU
-- name    : LeaderStyle.WageFloor.cost_FU
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:24.622759+00:00
-- url     : https://prove2.me/theorems/c5cec15e-7d38-47ea-81f7-e549586ada10
-- title:
--   §4.4, pp. 16–17 (PDF 18–19) — minimum cost under style FU
-- statement:
--   For carrot-and-stick leadership, the leader praises after high output and scolds after low output. The attained minimum total wage cost is
--
--   $$C_{FU}=\max\{\underline u+s,\underline w\}+c-\rho(s+r)+\rho k_F^h+(1-\rho)k_U^l+\underline u_l.$$
--
--   The expression combines the incentive gain from both actions with the participation cost of scolding and the leader's expected action costs.
-- source:
--   Dur, Kvaløy & Schöttner, Leadership Styles and Labor-Market Conditions, CRC TRR 190 Discussion Paper No. 278 (26 Feb 2021), pp. 16–17 (PDF 18–19), §4.4

import Mathlib
import Definitions.Def_LeaderStyle_WageFloor_Model

namespace LeaderStyle.WageFloor

theorem cost_FU (P : Params) (hS : P.Standing) :
    IsLeast (cost P '' {x : Contract | Feasible P .FU x})
      (max (P.ur + P.s) P.wf + P.c - P.rho * (P.s + P.r) +
        P.rho * P.kFh + (1 - P.rho) * P.kUl + P.ul) := by sorry
end LeaderStyle.WageFloor
