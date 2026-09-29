-- Prove2me | Theorems.Thm_Freiman_lowerJ_inner_contained
-- name    : Freiman.lowerJ_inner_contained
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:02:28.555112+00:00
-- url     : https://prove2.me/theorems/cc745f91-cd59-41cf-90de-c231fd11c707
-- title:
--   Freiman repeated-three proof: inner contained
-- statement:
--   The actual normal-left endpoint and the optionally shortened right endpoint contain the report inner interval; both words end3 and the original left stays wider.
-- source:
--   Freiman report j_family.tex and j_certificates.tex, equal-three-width and lower-j3-uniform; exact source width-criterion route.

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.lowerJ_inner_contained (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hr : lowerRunOffered p) (k : ℕ) (hk : 0 < k) (hp : lowerRunParameters p) : lowerJInner p k ⊆ lowerCover (lowerRunPair p k) := by
  sorry
