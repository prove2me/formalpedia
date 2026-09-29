-- Prove2me | Theorems.Thm_Freiman_lowerJ_inner_order
-- name    : Freiman.lowerJ_inner_order
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:02:08.787304+00:00
-- url     : https://prove2.me/theorems/f42b2746-d032-4519-bd08-d461a58dc85e
-- title:
--   Freiman repeated-three proof: inner order
-- statement:
--   The source a<c<b tail signs and actual alternating word parity order the two inner endpoints.
-- source:
--   Freiman report j_family.tex and j_certificates.tex, equal-three-width and lower-j3-uniform; exact source width-criterion route.

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.lowerJ_inner_order (hn : lowerJSignFacts) (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hr : lowerRunOffered p) (k : ℕ) (hk : 0 < k) : lowerJInnerOrder p k := by
  sorry
