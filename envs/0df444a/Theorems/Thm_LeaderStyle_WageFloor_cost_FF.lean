-- Prove2me | Theorems.Thm_LeaderStyle_WageFloor_cost_FF
-- name    : LeaderStyle.WageFloor.cost_FF
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:12.317685+00:00
-- url     : https://prove2.me/theorems/abb171a8-5146-4741-b07e-1a9581a6626b
-- title:
--   §4.2.2, p. 13 (PDF 15) — minimum cost under style FF
-- statement:
--   When the leader praises after either output, praise gives the worker $r$ independently of effort. With $k_F^h$ and $k_F^l$ denoting the leader's praise costs after high and low output, the attained minimum total wage cost is
--
--   $$C_{FF}=c+\max\{\underline u-r,\underline w\}+\rho k_F^h+(1-\rho)k_F^l+\underline u_l.$$
--
--   This cost captures how unconditional praise can lower the base salary until the wage floor binds.
-- source:
--   Dur, Kvaløy & Schöttner, Leadership Styles and Labor-Market Conditions, CRC TRR 190 Discussion Paper No. 278 (26 Feb 2021), p. 13 (PDF 15), §4.2.2, p. 13 (PDF 15)

import Mathlib
import Definitions.Def_LeaderStyle_WageFloor_Model

namespace LeaderStyle.WageFloor

theorem cost_FF (P : Params) (hS : P.Standing) :
    IsLeast (cost P '' {x : Contract | Feasible P .FF x})
      (P.c + max (P.ur - P.r) P.wf + P.rho * P.kFh +
        (1 - P.rho) * P.kFl + P.ul) := by sorry
end LeaderStyle.WageFloor
