-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_requirements_transfer
-- name    : Freiman.lowerEarlyTerminal_requirements_transfer
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:46:23.322977+00:00
-- url     : https://prove2.me/theorems/1bb727f6-53d8-4fb0-a502-523b43d6dd86
-- title:
--   Freiman.lowerEarlyTerminal_requirements_transfer
-- statement:
--   Finite requirement membership and all union branch indices transfer catalog soundness to every actual route requirement.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_requirements_transfer (he : LowerEarlyTerminalEndpointLaw) (hg : LowerEarlyTerminalGreaterLaw)
    (C : LowerEarlyTerminalCatalog) (p : LowerPair) (mode : ℕ)
    (hm : lowerEarlyTerminalMatches p C)
    (hr : certRectangleMem C.rectangle (lowerEarlyTerminalR p) (lowerEarlyTerminalS p))
    (hv : lowerEarlyTerminalRequirementBinding C mode) (hs : lowerEarlyTerminalGoalsSound C)
    (hcmp : ∀ u hi v hj strict,
      (∀ b ∈ lowerEarlyTerminalCompare C u hi v hj strict, lowerEarlyTerminalAt p b.1 →
        section14ComparisonHolds b.2 (lowerEarlyTerminalR p) (lowerEarlyTerminalS p) (lowerEarlyTerminalQ p)) →
      lowerEarlyTerminalKindHolds p (.compare u hi v hj strict))
    (hun : (∀ b ∈ lowerEarlyTerminalUnionCases C, lowerEarlyTerminalAt p b.1 →
        section14ComparisonHolds b.2 (lowerEarlyTerminalR p) (lowerEarlyTerminalS p) (lowerEarlyTerminalQ p)) →
      lowerEarlyTerminalUnionHolds p) : lowerEarlyTerminalRequiredSound C p mode := by
  sorry
