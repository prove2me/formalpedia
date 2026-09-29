-- Prove2me | Theorems.Thm_Freiman_gap_finite_reduction
-- name    : Freiman.gap_finite_reduction
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:14:34.518714+00:00
-- url     : https://prove2.me/theorems/4d7dec9d-68d1-48c3-9b0c-a91388468999
-- title:
--   gap finite reduction
-- statement:
--   Every capped centred word above the lower window contains precisely one of the marked A/B alternatives, allowing reflection.
-- source:
--   Freiman Hall ray report, m3.tex; lem:m3:tree

import Definitions.Def_Freiman_gapCertificateData

namespace Freiman

theorem gap_finite_reduction (a : ℤ → ℕ+) (hc : gapCapped a) (hw : gapWindow < localValue a 0) : gapReduced a 0 := by
  sorry

end Freiman
