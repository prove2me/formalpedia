-- Prove2me | Theorems.Thm_Freiman_background_constant_order
-- name    : Freiman.background_constant_order
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:27.876121+00:00
-- url     : https://prove2.me/theorems/aaade462-71f6-4b76-a78a-e0e161706820
-- title:
--   background constant order
-- statement:
--   The exact constants obey $9/2<c_*<113195/25000<c_F$. The report supplies explicit positive integer differences after squaring positive quantities.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, §1.4, found:constant-order and the four integer certificates immediately following it.

import Definitions.Def_Freiman_wordRealization
import Definitions.Def_Freiman_cF

open Freiman

theorem Freiman.background_constant_order  :
    (9 / 2 : ℝ) < 4 * Real.sqrt 462 / 19 ∧ 4 * Real.sqrt 462 / 19 < (113195 / 25000 : ℝ) ∧ (113195 / 25000 : ℝ) < cF := by sorry
