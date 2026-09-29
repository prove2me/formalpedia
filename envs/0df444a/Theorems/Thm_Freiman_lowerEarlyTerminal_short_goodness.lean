-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_short_goodness
-- name    : Freiman.lowerEarlyTerminal_short_goodness
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:49:13.624866+00:00
-- url     : https://prove2.me/theorems/be27fc1b-57d1-4281-9699-18fa40d54268
-- title:
--   Freiman.lowerEarlyTerminal_short_goodness
-- statement:
--   Interior strict goodness checks plus the separately certified inherited anchors supply every short-route cover.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_short_goodness (C : LowerEarlyTerminalCatalog) (p : LowerPair) (mode : ℕ) (hm : mode<2)
    (hb : if mode=0 then lowerA p 27 else ¬ lowerA p 27 ∧ lowerA p 34)
    (h : lowerEarlyTerminalRequiredSound C p mode) (ha : lowerEarlyTerminalAt p (lowerEarlyTerminalHyp C mode))
    (hn : ∀ w : LowerPair, (lowerCover w).Nonempty)
    (hgood : ∀ l, lowerEarlyTerminalNative p l → (∀ req ∈ lowerEarlyTerminalGoodRequirements [] l, lowerEarlyTerminalAt p req.1 →
      lowerEarlyTerminalKindHolds p req.2) → lowerGood (lowerChild p l))
    (hanchors : lowerGood (lowerChild p ([3],[2])) ∧ lowerGood (lowerChild p ([2],[2]))) :
    lowerEarlyTerminalLabelsGood p (if mode=0 then lowerEarlyTerminalFirst else lowerEarlyTerminalSecond) := by
  sorry
