-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_required_sound
-- name    : Freiman.lowerEarlyTerminal_required_sound
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:46:25.851474+00:00
-- url     : https://prove2.me/theorems/f50e7507-4956-44d9-9d43-bb597dfb2025
-- title:
--   Freiman.lowerEarlyTerminal_required_sound
-- statement:
--   Assemble endpoint semantics, exact pair catalog soundness and source requirement binding.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_required_sound (C : LowerEarlyTerminalCatalog) (p : LowerPair) (mode : ℕ)
    (hm : lowerEarlyTerminalMatches p C)
    (hr : certRectangleMem C.rectangle (lowerEarlyTerminalR p) (lowerEarlyTerminalS p))
    (hv : lowerEarlyTerminalFiniteValid C) (hb : lowerEarlyTerminalRequirementBinding C mode) :
    lowerEarlyTerminalRequiredSound C p mode := by
  sorry
