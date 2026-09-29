-- Prove2me | Theorems.Thm_Freiman_localValue_shift
-- name    : Freiman.localValue_shift
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:25.037979+00:00
-- url     : https://prove2.me/theorems/d08765e0-0f98-4a82-b97d-82c07334dcfc
-- title:
--   localValue shift
-- statement:
--   Local Perron values commute with integer shifts of the two-sided word. This is the explicit index bridge used when a limiting word is a shifted original word.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, §1.1, equation found:local-values, and §1.6 bounded-distance case.

import Definitions.Def_Freiman_wordRealization

open Freiman

theorem Freiman.localValue_shift (a : ℤ → ℕ+) (s i : ℤ) :
    localValue (fun k : ℤ => a (s + k)) i = localValue a (s + i) := by sorry
