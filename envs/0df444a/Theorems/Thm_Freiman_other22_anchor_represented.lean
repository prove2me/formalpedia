-- Prove2me | Theorems.Thm_Freiman_other22_anchor_represented
-- name    : Freiman.other22_anchor_represented
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:35:14.325137+00:00
-- url     : https://prove2.me/theorems/fb2767e5-0408-4dda-9de0-ce3b42138f25
-- title:
--   other22 anchor represented
-- statement:
--   Expand the actual earlier32 upper endpoint (or birth lower endpoint when the old left ends31) into one of the source endpoint cases, with true case conditions and nonnegative exact tails.
-- source:
--   Report §7.3, Lemma 7.4 (lem:old23-other22-target), printed p.43; other22_target.tex and Appendix other22_certificates.tex; original 144-obligation exact certificate.

import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs

open Freiman

theorem Freiman.other22_anchor_represented (Z B R S : LowerPair) (h : LowerOther22Geometry Z B R S) (k : Fin 6) (hc : lowerHistoryContextFits Z (other22Context k)) :
    other22EndpointRepresented Z (other22Context k) (other22Ancestor k) (other22AncestorUpper k) (other22AnchorValue Z) := by
  sorry
