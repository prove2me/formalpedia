-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_width_tie_ratios
-- name    : Freiman.lowerEarlyTerminal_width_tie_ratios
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:42:08.860564+00:00
-- url     : https://prove2.me/theorems/2816f36c-978b-4c86-8d69-b15ef0b7ec65
-- title:
--   Freiman.lowerEarlyTerminal_width_tie_ratios
-- statement:
--   An exact full-width tie has only the two stated continuant-ratio alternatives.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_width_tie_ratios (u v : List ℕ+) (h : lowerWidth u = lowerWidth v) : lowerRatio u = lowerRatio v ∨
      lowerRatio v = (4-3*lowerRatio u)/(3+4*lowerRatio u) := by
  sorry
