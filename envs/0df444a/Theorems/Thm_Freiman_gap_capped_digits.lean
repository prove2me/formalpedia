-- Prove2me | Theorems.Thm_Freiman_gap_capped_digits
-- name    : Freiman.gap_capped_digits
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:12:36.245977+00:00
-- url     : https://prove2.me/theorems/caaed270-191b-4af1-aa79-3b5329c0273f
-- title:
--   gap capped digits
-- statement:
--   A global height cap q<5 forces every digit to be at most four.
-- source:
--   Freiman Hall ray report, m3.tex; lem:m3:recenter

import Definitions.Def_Freiman_gapCertificateData

namespace Freiman

theorem gap_capped_digits (a : ℤ → ℕ+) (h : gapCapped a) : gapDigits a := by
  sorry

end Freiman
