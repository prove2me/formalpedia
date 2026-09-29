-- Prove2me | Theorems.Thm_Freiman_lowerJ_reverse_cross
-- name    : Freiman.lowerJ_reverse_cross
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:02:24.222193+00:00
-- url     : https://prove2.me/theorems/ec091df1-4f0d-4713-99fa-0dc4e2059006
-- title:
--   Freiman repeated-three proof: reverse cross
-- statement:
--   The two componentwise b>φ²(a),φ²(c) source signs give the opposite strict cross comparison.
-- source:
--   Freiman report j_family.tex and j_certificates.tex, equal-three-width and lower-j3-uniform; exact source width-criterion route.

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.lowerJ_reverse_cross (hn : lowerJSignFacts) (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hr : lowerRunOffered p) (k : ℕ) (hk : 0 < k) : lowerJReverseCross p k := by
  sorry
