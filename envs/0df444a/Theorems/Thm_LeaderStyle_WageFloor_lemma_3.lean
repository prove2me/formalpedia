-- Prove2me | Theorems.Thm_LeaderStyle_WageFloor_lemma_3
-- name    : LeaderStyle.WageFloor.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:29.439923+00:00
-- url     : https://prove2.me/theorems/f9350d38-a13d-4f08-9e6a-ca41c8a00685
-- title:
--   Lemma 3, p. 16 (PDF 18) — conditional scolding versus monetary incentives
-- statement:
--   Conditional scolding is strictly cheaper than pure monetary incentives exactly when
--
--   $$(1-\rho)k_U^l+\max\{s-(\underline w-\underline u),0\}<\rho s\quad\text{(U)}.$$
--
--   When (U) holds, the wage floor is strictly above the worker's reservation utility: $\underline u<\underline w$. The condition captures the rent that can absorb the worker's disutility from scolding.
--
--   **Formalization Note** The equivalence also holds for competitive wage-setting, where both sides are false. The rent and welfare clauses of the printed lemma are outside this item.
-- source:
--   Dur, Kvaløy & Schöttner, Leadership Styles and Labor-Market Conditions, CRC TRR 190 Discussion Paper No. 278 (26 Feb 2021), p. 16 (PDF 18), Lemma 3, p. 16 (PDF 18)

import Mathlib
import Definitions.Def_LeaderStyle_WageFloor_Model

namespace LeaderStyle.WageFloor

theorem lemma_3 (P : Params) (hS : P.Standing) :
    (Prefers P .U .none ↔ condU P) ∧
      (condU P → P.ur < P.wf) := by sorry
end LeaderStyle.WageFloor
