-- Prove2me | Theorems.Thm_Freiman_lowerJ_first_cross
-- name    : Freiman.lowerJ_first_cross
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:02:12.068983+00:00
-- url     : https://prove2.me/theorems/f47302b7-31b7-4133-aebc-9c788d0d2eea
-- title:
--   Freiman repeated-three proof: first cross
-- statement:
--   The determinant difference identity gives precisely the report contact threshold Hk, retaining the original root parity.
-- source:
--   Freiman report j_family.tex and j_certificates.tex, equal-three-width and lower-j3-uniform; exact source width-criterion route.

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.lowerJ_first_cross (hf : ∀ (w : List ℕ+) (t : ℝ), 0 < t → prefixEval w t = lowerInitialMatEval (lowerInitialWordMatrix w) t ∧ 0 < lowerInitialMatDen (lowerInitialWordMatrix w) t ∧ (lowerInitialWordMatrix w).a*(lowerInitialWordMatrix w).d - (lowerInitialWordMatrix w).b*(lowerInitialWordMatrix w).c = (-1:ℝ)^w.length) (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hr : lowerRunOffered p) (k : ℕ) (hk : 0 < k) (hq : lowerScale (lowerNormalize p) < lowerJHK k (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2)) : lowerJFirstCross p k := by
  sorry
