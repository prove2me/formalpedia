-- Prove2me | Theorems.Thm_LeaderStyle_WageFloor_proposition_2
-- name    : LeaderStyle.WageFloor.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:30.755165+00:00
-- url     : https://prove2.me/theorems/7a602f6a-afa6-4055-a192-f1d077222928
-- title:
--   Proposition 2, p. 18 (PDF 20) — optimal style under a binding wage floor
-- statement:
--   Suppose the wage floor $\underline w$ exceeds the worker's reservation utility $\underline u$. Across all six feasible styles, the principal can choose a minimum-cost contract by the following cases. Put $a=k_F^h/r$, $d=k_U^l/s$, $t=\rho/(1-\rho)$, and let (U′) mean $(1-\rho)(s+k_U^l)<\underline w-\underline u$.
--
--   1. If $a\ge1$ and $d\ge t$, pure monetary incentives are optimal.
--   2. If $a<1$, style FU is optimal when $d<t$ and (U′) holds; otherwise style F is optimal.
--   3. If neither earlier case applies, style U is optimal when (U′) holds; otherwise pure monetary incentives are optimal.
--
--   The result classifies the principal's least-cost style under noncompetitive wage-setting.
--
--   **Formalization Note** “Implements” and “dominates the adoption” mean attainment of a weak minimum over feasible contracts of all six styles. Ties are allowed. The ratios have positive denominators under the standing model assumptions.
-- source:
--   Dur, Kvaløy & Schöttner, Leadership Styles and Labor-Market Conditions, CRC TRR 190 Discussion Paper No. 278 (26 Feb 2021), p. 18 (PDF 20), Proposition 2

import Mathlib
import Definitions.Def_LeaderStyle_WageFloor_Model

namespace LeaderStyle.WageFloor

theorem proposition_2 (P : Params) (hS : P.Standing) (hnc : P.ur < P.wf) :
    (1 ≤ P.kFh / P.r ∧ P.rho / (1 - P.rho) ≤ P.kUl / P.s → IsOptimalStyle P .none) ∧
    (P.kFh / P.r < 1 →
      (P.kUl / P.s < P.rho / (1 - P.rho) ∧ condU' P → IsOptimalStyle P .FU) ∧
      (¬ (P.kUl / P.s < P.rho / (1 - P.rho) ∧ condU' P) → IsOptimalStyle P .F)) ∧
    (¬ (1 ≤ P.kFh / P.r ∧ P.rho / (1 - P.rho) ≤ P.kUl / P.s) →
      ¬ (P.kFh / P.r < 1) →
      (condU' P → IsOptimalStyle P .U) ∧
      (¬ condU' P → IsOptimalStyle P .none)) := by sorry
end LeaderStyle.WageFloor
