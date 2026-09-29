-- Prove2me | Theorems.Thm_Freiman_gap_match_alignment
-- name    : Freiman.gap_match_alignment
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:12:43.089763+00:00
-- url     : https://prove2.me/theorems/c4381f92-4e8e-4bcf-b374-1643e9640080
-- title:
--   gap match alignment
-- statement:
--   Aligned containment of a marked finite word preserves its distinguished coordinate.
-- source:
--   Freiman Hall ray report, m3.tex; finite partition semantics

import Definitions.Def_Freiman_gapCertificateData

namespace Freiman

theorem gap_match_alignment (a : ℤ → ℕ+) (i : ℤ) (s v : GapState) (hm : gapMatch a i s) (hv : v.centre < v.word.length) (hc : gapAlignedContains s v) : gapMatch a i v := by
  sorry

end Freiman
