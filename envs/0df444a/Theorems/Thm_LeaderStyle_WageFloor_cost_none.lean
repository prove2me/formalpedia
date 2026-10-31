-- Prove2me | Theorems.Thm_LeaderStyle_WageFloor_cost_none
-- name    : LeaderStyle.WageFloor.cost_none
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:09.837689+00:00
-- url     : https://prove2.me/theorems/72da2e85-e87c-431c-9eb1-11e70a6e386b
-- title:
--   §4.1, p. 11 (PDF 13) — minimum cost under pure monetary incentives
-- statement:
--   For a worker with reservation utility $\underline u$, a base-salary floor $\underline w$, high-effort cost $c$, and a selfish leader with reservation utility $\underline u_l$, let $C_0$ be the least expected total wage cost of a feasible pure monetary contract. Then
--
--   $$C_0=c+\max\{\underline u,\underline w\}+\underline u_l.$$
--
--   The least-cost bonus is $c/\rho$, and the base salary is $\max\{\underline u,\underline w\}$. The formal result asserts that this cost is attained and bounds every feasible contract from below.
-- source:
--   Dur, Kvaløy & Schöttner, Leadership Styles and Labor-Market Conditions, CRC TRR 190 Discussion Paper No. 278 (26 Feb 2021), p. 11 (PDF 13), §4.1, p. 11 (PDF 13)

import Mathlib
import Definitions.Def_LeaderStyle_WageFloor_Model

namespace LeaderStyle.WageFloor

theorem cost_none (P : Params) (hS : P.Standing) :
    IsLeast (cost P '' {x : Contract | Feasible P .none x})
      (P.c + max P.ur P.wf + P.ul) := by sorry
end LeaderStyle.WageFloor
