-- Prove2me | Theorems.Thm_LeaderStyle_WageFloor_lemma_1
-- name    : LeaderStyle.WageFloor.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:16.831466+00:00
-- url     : https://prove2.me/theorems/d2b95420-b1a0-416a-8c14-2b88191384b2
-- title:
--   Lemma 1, p. 13 (PDF 15) — conditional praise versus monetary incentives
-- statement:
--   For every reservation utility $\underline u$ and wage floor $\underline w$, conditional praise is strictly cheaper for the principal than pure monetary incentives exactly when its benefit to the worker exceeds its cost to the leader:
--
--   $$C_F<C_0\quad\Longleftrightarrow\quad k_F^h<r\quad\text{(F)}.$$
--
--   Here strict preference means that one feasible F contract costs less than every feasible monetary contract. This comparison isolates the efficiency of praise from labor-market conditions.
--
--   **Formalization Note** Lemma 1 says “if”; the displayed cost formulas also give the converse, so this item states the equivalent comparison. The lemma's separate worker-rent clause is outside this item.
-- source:
--   Dur, Kvaløy & Schöttner, Leadership Styles and Labor-Market Conditions, CRC TRR 190 Discussion Paper No. 278 (26 Feb 2021), p. 13 (PDF 15), Lemma 1, p. 13 (PDF 15)

import Mathlib
import Definitions.Def_LeaderStyle_WageFloor_Model

namespace LeaderStyle.WageFloor

theorem lemma_1 (P : Params) (hS : P.Standing) :
    Prefers P .F .none ↔ condF P := by sorry
end LeaderStyle.WageFloor
