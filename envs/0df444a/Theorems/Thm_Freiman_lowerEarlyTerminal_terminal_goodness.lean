-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_terminal_goodness
-- name    : Freiman.lowerEarlyTerminal_terminal_goodness
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:51:25.608601+00:00
-- url     : https://prove2.me/theorems/b60c119a-a1b2-4726-8c7f-23749951006c
-- title:
--   Freiman.lowerEarlyTerminal_terminal_goodness
-- statement:
--   Choose the actual A40 alternative, and combine all15 interior goodness checks with both inherited anchors.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_terminal_goodness (hp : LowerEarlyTerminalParameterLaws) (C : LowerEarlyTerminalCatalog) (p : LowerPair)
    (h27 : ¬ lowerA p 27) (h34 : ¬ lowerA p 34)
    (h : lowerEarlyTerminalRequiredSound C p 2) (ha : lowerEarlyTerminalAt p (lowerEarlyTerminalHyp C 2))
    (hn : ∀ w : LowerPair, (lowerCover w).Nonempty)
    (hgood : ∀ l, lowerEarlyTerminalNative p l → (∀ req ∈ lowerEarlyTerminalGoodRequirements [] l, lowerEarlyTerminalAt p req.1 →
      lowerEarlyTerminalKindHolds p req.2) → lowerGood (lowerChild p l))
    (hanchors : lowerGood (lowerChild p ([3],[2])) ∧ lowerGood (lowerChild p ([2],[2]))) :
    lowerEarlyTerminalLabelsGood p (lowerEarlyTerminalTerminal (lowerEarlyTerminalPrimary p)) := by
  sorry
