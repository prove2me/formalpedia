-- Prove2me | Theorems.Thm_LeaderStyle_WageFloor_lemma_2
-- name    : LeaderStyle.WageFloor.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:15.038982+00:00
-- url     : https://prove2.me/theorems/1d7d67d4-eb77-44c0-8d06-b8875fbaa90a
-- title:
--   Lemma 2, p. 14 (PDF 16) — unconditional praise versus monetary incentives
-- statement:
--   Let $k_F^h$ and $k_F^l$ be the leader's costs of praise following high and low output. Unconditional praise is strictly cheaper than pure monetary incentives exactly when
--
--   $$\rho k_F^h+(1-\rho)k_F^l<\min\{r,\underline u-\underline w\}\quad\text{(FF)}.$$
--
--   Condition (FF) can hold only when $\underline w\le\underline u$, the competitive wage-setting regime. The result identifies when reduced base pay covers the leader's expected praise cost.
--
--   **Formalization Note** The paper's additional worker-utility and welfare clauses are outside this item.
-- source:
--   Dur, Kvaløy & Schöttner, Leadership Styles and Labor-Market Conditions, CRC TRR 190 Discussion Paper No. 278 (26 Feb 2021), p. 14 (PDF 16), Lemma 2, p. 14 (PDF 16)

import Mathlib
import Definitions.Def_LeaderStyle_WageFloor_Model

namespace LeaderStyle.WageFloor

theorem lemma_2 (P : Params) (hS : P.Standing) :
    (Prefers P .FF .none ↔ condFF P) ∧
      (condFF P → P.wf ≤ P.ur) := by sorry
end LeaderStyle.WageFloor
