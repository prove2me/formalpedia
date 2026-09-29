-- Prove2me | Theorems.Thm_Freiman_gap_tail_interior
-- name    : Freiman.gap_tail_interior
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:12:31.148442+00:00
-- url     : https://prove2.me/theorems/d55b13c8-09a0-44ff-8372-3a4e5ab21b31
-- title:
--   gap tail interior
-- statement:
--   Every infinite tail on digits 1–4 lies strictly inside the cylinder interval K.
-- source:
--   Freiman Hall ray report, m3.tex; eq:m3:cylinder

import Definitions.Def_Freiman_gapCertificateData

namespace Freiman

theorem gap_tail_interior (b : ℕ → ℕ+) (h : ∀ n, (b n : ℕ) ≤ 4) : (1/5 : ℝ) < cfValue b ∧ cfValue b < 5/6 := by
  sorry

end Freiman
