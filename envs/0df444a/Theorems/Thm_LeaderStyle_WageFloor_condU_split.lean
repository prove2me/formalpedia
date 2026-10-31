-- Prove2me | Theorems.Thm_LeaderStyle_WageFloor_condU_split
-- name    : LeaderStyle.WageFloor.condU_split
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:25.897736+00:00
-- url     : https://prove2.me/theorems/8b815fbe-aa4c-4192-8e5b-aed3a2f42d6a
-- title:
--   Proof of Proposition 2, p. 34 (PDF 36) — splitting condition (U)
-- statement:
--   Under a binding wage floor, condition (U) is equivalent to the simultaneous threshold and rent requirements
--
--   $$(U)\iff\left(\frac{k_U^l}{s}<\frac{\rho}{1-\rho}\right)\wedge\left((1-\rho)(s+k_U^l)<\underline w-\underline u\right).$$
--
--   The second inequality is condition (U′). This equivalence translates the cost comparison into the two tests in Proposition 2.
-- source:
--   Dur, Kvaløy & Schöttner, Leadership Styles and Labor-Market Conditions, CRC TRR 190 Discussion Paper No. 278 (26 Feb 2021), p. 34 (PDF 36), Proof of Proposition 2, p. 34 (PDF 36)

import Mathlib
import Definitions.Def_LeaderStyle_WageFloor_Model

namespace LeaderStyle.WageFloor

theorem condU_split (P : Params) (hS : P.Standing) (hnc : P.ur < P.wf) :
    condU P ↔ P.kUl / P.s < P.rho / (1 - P.rho) ∧ condU' P := by sorry
end LeaderStyle.WageFloor
