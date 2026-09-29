-- Prove2me | Theorems.Thm_Freiman_gap_window_match
-- name    : Freiman.gap_window_match
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:15:14.907583+00:00
-- url     : https://prove2.me/theorems/27e34ec4-7713-4cac-9ae3-fcaa7490caaf
-- title:
--   gap window match
-- statement:
--   The finite radius-r window definition matches its physical two-sided word and marked coordinate.
-- source:
--   Freiman Hall ray report, m3.tex; eq:m3:cylinder

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_window_match (a : ℤ → ℕ+) (i : ℤ) (r : ℕ) : gapMatch a i ⟨gapLocalWindow a i r,r⟩ := by
  sorry

end Freiman
