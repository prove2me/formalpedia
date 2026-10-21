-- Prove2me | Theorems.Thm_LeaderStyle_WageFloor_cost_U
-- name    : LeaderStyle.WageFloor.cost_U
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:16.277514+00:00
-- url     : https://prove2.me/theorems/1871c152-c238-471c-8f17-61d95a5fdc50
-- title:
--   §4.3.1, p. 15 (PDF 17) — minimum cost under style U
-- statement:
--   When the leader scolds after low output, let $s$ be the worker's disutility and $k_U^l$ the leader's cost of scolding. The attained minimum total wage cost of a feasible conditional unfriendly contract is
--
--   $$C_U=\max\{\underline u+s,\underline w\}+c-\rho s+(1-\rho)k_U^l+\underline u_l.$$
--
--   The formula records both the bonus reduction and the possible increase in base salary needed for participation.
-- source:
--   Dur, Kvaløy & Schöttner, Leadership Styles and Labor-Market Conditions, CRC TRR 190 Discussion Paper No. 278 (26 Feb 2021), p. 15 (PDF 17), §4.3.1, p. 15 (PDF 17)

import Mathlib
import Definitions.Def_LeaderStyle_WageFloor_Model

namespace LeaderStyle.WageFloor

theorem cost_U (P : Params) (hS : P.Standing) :
    IsLeast (cost P '' {x : Contract | Feasible P .U x})
      (max (P.ur + P.s) P.wf + P.c - P.rho * P.s +
        (1 - P.rho) * P.kUl + P.ul) := by sorry
end LeaderStyle.WageFloor
