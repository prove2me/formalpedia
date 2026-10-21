-- Prove2me | Theorems.Thm_LeaderStyle_WageFloor_FU_comparisons
-- name    : LeaderStyle.WageFloor.FU_comparisons
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:18.074051+00:00
-- url     : https://prove2.me/theorems/0529bf59-f69a-4a0d-a878-4892bb2c60bd
-- title:
--   §4.4, p. 17 (PDF 19) — FU against U and F
-- statement:
--   Adding conditional praise to style U strictly lowers the principal's minimum cost exactly when condition (F) holds. Adding conditional scolding to style F strictly lowers it exactly when condition (U) holds:
--
--   $$C_{FU}<C_U\iff k_F^h<r,\qquad C_{FU}<C_F\iff (U).$$
--
--   These comparisons identify when each component of carrot-and-stick leadership improves on its single-action counterpart.
--
--   **Formalization Note** The two comparisons are stated without the paper's introductory supposition that the starting style already beats the monetary benchmark; the displayed cost identities hold for all standing parameters.
-- source:
--   Dur, Kvaløy & Schöttner, Leadership Styles and Labor-Market Conditions, CRC TRR 190 Discussion Paper No. 278 (26 Feb 2021), p. 17 (PDF 19), §4.4, p. 17 (PDF 19)

import Mathlib
import Definitions.Def_LeaderStyle_WageFloor_Model

namespace LeaderStyle.WageFloor

theorem FU_comparisons (P : Params) (hS : P.Standing) :
    (Prefers P .FU .U ↔ condF P) ∧
      (Prefers P .FU .F ↔ condU P) := by sorry
end LeaderStyle.WageFloor
