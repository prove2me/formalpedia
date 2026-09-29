-- Prove2me | Theorems.Thm_Freiman_gap_lower_checks
-- name    : Freiman.gap_lower_checks
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:12:49.984664+00:00
-- url     : https://prove2.me/theorems/76f20c53-6ac2-4e26-865b-5e72f3d6755d
-- title:
--   gap lower checks
-- statement:
--   The checked lower-row rules use only rows with smaller index; there is no circular gap assumption.
-- source:
--   Freiman Hall ray report, m3.tex; lem:m3:tables

import Definitions.Def_Freiman_gapCertificateData

namespace Freiman

theorem gap_lower_checks : ∀ n : ℕ, n < 19 → gapChecks (gapLowerRows.take n) [] .forbidden (gapLowerTrees[n]!) := by
  sorry

end Freiman
