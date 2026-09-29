-- Prove2me | Theorems.Thm_Freiman_lower_child_normalize
-- name    : Freiman.lower_child_normalize
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:22:45.364685+00:00
-- url     : https://prove2.me/theorems/4b5bb01d-d3ff-42ad-b24b-c8f2a9e0d062
-- title:
--   Freiman lower construction: child normalize
-- statement:
--   Normalizing the parent twice is idempotent with incoming order retained at equality; this is not an assertion that a tied cover is invariant under swapping.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_child_normalize (p : LowerPair) (l : LowerLabel) : lowerChild (lowerNormalize p) l = lowerChild p l := by
  sorry
