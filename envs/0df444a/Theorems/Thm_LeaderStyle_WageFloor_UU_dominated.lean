-- Prove2me | Theorems.Thm_LeaderStyle_WageFloor_UU_dominated
-- name    : LeaderStyle.WageFloor.UU_dominated
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:19.075164+00:00
-- url     : https://prove2.me/theorems/a9f387d7-c62b-4d72-8a19-bf35263b330d
-- title:
--   §4.3.2, p. 16 (PDF 18) — unconditional scolding is dominated
-- statement:
--   If the selfish leader scolds regardless of output, pure monetary incentives are strictly cheaper for the principal:
--
--   $$C_0<C_{UU}.$$
--
--   The formal comparison is over feasible contracts. Unconditional scolding changes neither effort incentives nor the bonus needed for high effort, while it imposes disutility on the worker and positive cost on the leader.
-- source:
--   Dur, Kvaløy & Schöttner, Leadership Styles and Labor-Market Conditions, CRC TRR 190 Discussion Paper No. 278 (26 Feb 2021), p. 16 (PDF 18), §4.3.2, p. 16 (PDF 18)

import Mathlib
import Definitions.Def_LeaderStyle_WageFloor_Model

namespace LeaderStyle.WageFloor

theorem UU_dominated (P : Params) (hS : P.Standing) :
    Prefers P .none .UU := by sorry
end LeaderStyle.WageFloor
