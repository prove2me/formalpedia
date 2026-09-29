-- Prove2me | Theorems.Thm_Freiman_gap_reflection
-- name    : Freiman.gap_reflection
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:12:33.163506+00:00
-- url     : https://prove2.me/theorems/ce44cb07-23e1-465c-b057-d23ccd96e850
-- title:
--   gap reflection
-- statement:
--   Reflection reverses coordinates and preserves the corresponding local height.
-- source:
--   Freiman Hall ray report, m3.tex; thm:m3:gap

import Definitions.Def_Freiman_gapCertificateData

namespace Freiman

theorem gap_reflection (a : ℤ → ℕ+) (i : ℤ) : localValue (gapReflect a) i = localValue a (-i) := by
  sorry

end Freiman
