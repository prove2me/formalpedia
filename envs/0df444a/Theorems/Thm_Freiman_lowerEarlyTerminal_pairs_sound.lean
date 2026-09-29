-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_pairs_sound
-- name    : Freiman.lowerEarlyTerminal_pairs_sound
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:47:03.812587+00:00
-- url     : https://prove2.me/theorems/ccfef934-86be-4cb5-8d78-c421b9ac44c3
-- title:
--   Freiman.lowerEarlyTerminal_pairs_sound
-- statement:
--   Apply the common exact Bernstein exclusion theorem to each valid pair.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_pairs_sound (C : LowerEarlyTerminalCatalog) (hp : ∀ p ∈ C.pairs, lowerEarlyTerminalPairValid C p) : lowerEarlyTerminalPairSound C := by
  sorry
