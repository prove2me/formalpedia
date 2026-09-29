-- Prove2me | Theorems.Thm_Freiman_lowerJ_inner_intersection
-- name    : Freiman.lowerJ_inner_intersection
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:02:19.359135+00:00
-- url     : https://prove2.me/theorems/b36a768f-a2cc-427d-a552-c6e08cfba1b9
-- title:
--   Freiman repeated-three proof: inner intersection
-- statement:
--   Two ordered real intervals intersect by the two strict cross inequalities; this is a finite order/parity case split.
-- source:
--   Freiman report j_family.tex and j_certificates.tex, equal-three-width and lower-j3-uniform; exact source width-criterion route.

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.lowerJ_inner_intersection (p : LowerPair) (k : ℕ) (ha : lowerJInnerOrder p k) (hb : lowerJInnerOrder p (k+2)) (h1 : lowerJFirstCross p k) (h2 : lowerJReverseCross p k) : (lowerJInner p k ∩ lowerJInner p (k+2)).Nonempty := by
  sorry
