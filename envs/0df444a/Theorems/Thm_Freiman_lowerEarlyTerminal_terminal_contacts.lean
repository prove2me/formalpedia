-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_terminal_contacts
-- name    : Freiman.lowerEarlyTerminal_terminal_contacts
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:50:26.445502+00:00
-- url     : https://prove2.me/theorems/d881994a-6715-44da-917a-2425a5af9255
-- title:
--   Freiman.lowerEarlyTerminal_terminal_contacts
-- statement:
--   Read the11 common contacts, two A40 bridges, the A46 choice and the final union join from explicit source requirements.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_terminal_contacts (hp : LowerEarlyTerminalParameterLaws) (C : LowerEarlyTerminalCatalog) (p : LowerPair)
    (h : lowerEarlyTerminalRequiredSound C p 2) (ha : lowerEarlyTerminalAt p (lowerEarlyTerminalHyp C 2))
    (ho : ∀ w : LowerPair, lowerEndpoint w false ≤ lowerEndpoint w true)
    (hcontact : ∀ a b, lowerEarlyTerminalKindHolds p (.compare (section14LabelWords a) true (section14LabelWords b) false false) →
      lowerEarlyTerminalKindHolds p (.compare (section14LabelWords b) true (section14LabelWords a) false false) →
      lowerEarlyTerminalContact p a b)
    (hu : ∀ a b c, lowerEarlyTerminalContact p b c →
      (lowerEarlyTerminalEndpoint p (section14LabelWords b) false ≤ lowerEarlyTerminalEndpoint p (section14LabelWords a) true ∨
        lowerEarlyTerminalEndpoint p (section14LabelWords c) false ≤ lowerEarlyTerminalEndpoint p (section14LabelWords a) true) →
      lowerEarlyTerminalEndpoint p (section14LabelWords a) false ≤ lowerEarlyTerminalEndpoint p (section14LabelWords c) true →
      (lowerCover (lowerChild p a) ∩ (lowerCover (lowerChild p b) ∪ lowerCover (lowerChild p c))).Nonempty)
    (hl : lowerEarlyTerminalLabelsGood p (lowerEarlyTerminalTerminal (lowerEarlyTerminalPrimary p))) :
    lowerEarlyTerminalTerminalData p (lowerEarlyTerminalPrimary p) := by
  sorry
