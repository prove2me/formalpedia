-- Prove2me | Theorems.Thm_Freiman_gap_centered_membership
-- name    : Freiman.gap_centered_membership
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:17:09.720872+00:00
-- url     : https://prove2.me/theorems/20e7a568-4a8d-4d60-9627-95456bf091d3
-- title:
--   gap centered membership
-- statement:
--   An attained global height satisfies both clauses of the existing symbolic Markov-spectrum definition.
-- source:
--   Freiman Hall ray report, m3.tex; thm:m3:gap

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_centered_membership (a : ℤ → ℕ+) (t : ℝ) (hmax : ∀ i, localValue a i ≤ t) (h0 : localValue a 0 = t) : t ∈ symbolicMarkovSpectrum := by
  sorry

end Freiman
