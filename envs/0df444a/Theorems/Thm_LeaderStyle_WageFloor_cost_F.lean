-- Prove2me | Theorems.Thm_LeaderStyle_WageFloor_cost_F
-- name    : LeaderStyle.WageFloor.cost_F
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:14.205531+00:00
-- url     : https://prove2.me/theorems/7978d03c-c605-4d2a-9fe6-7c35c6e15c76
-- title:
--   §4.2.1, p. 12 (PDF 14) — minimum cost under style F
-- statement:
--   Let $\rho$ be the high-output probability under high effort, $r$ the worker's value of praise after high output, and $k_F^h$ the leader's cost of giving it. The minimum total wage cost of a feasible conditional friendly contract is
--
--   $$C_F=c-\rho(r-k_F^h)+\max\{\underline u,\underline w\}+\underline u_l.$$
--
--   This attained cost measures the effect of substituting praise for a portion of the worker's bonus.
-- source:
--   Dur, Kvaløy & Schöttner, Leadership Styles and Labor-Market Conditions, CRC TRR 190 Discussion Paper No. 278 (26 Feb 2021), p. 12 (PDF 14), §4.2.1, p. 12 (PDF 14)

import Mathlib
import Definitions.Def_LeaderStyle_WageFloor_Model

namespace LeaderStyle.WageFloor

theorem cost_F (P : Params) (hS : P.Standing) :
    IsLeast (cost P '' {x : Contract | Feasible P .F x})
      (P.c - P.rho * (P.r - P.kFh) + max P.ur P.wf + P.ul) := by sorry
end LeaderStyle.WageFloor
