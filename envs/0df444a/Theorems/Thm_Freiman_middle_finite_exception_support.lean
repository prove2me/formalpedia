-- Prove2me | Theorems.Thm_Freiman_middle_finite_exception_support
-- name    : Freiman.middle_finite_exception_support
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:08:59.399253+00:00
-- url     : https://prove2.me/theorems/07d0b0ea-c0da-4e1e-bde2-25012f13d8ca
-- title:
--   middle finite exception support
-- statement:
--   A completion differs from the background alphabet {1,2,3} only in its finite fixed core; choose a radius beyond both fixed outward word lengths.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:prop:path and Lagrange realization section

import Definitions.Def_Freiman_middleRoots

namespace Freiman

theorem middle_finite_exception_support :
    ∀ (c : MiddleCore) (a : ℤ→ℕ+), middleCompatible c a → ∃ N : ℕ, ∀ i : ℤ, N ≤ i.natAbs → (a i:ℕ) ≤ 3 := by
  sorry

end Freiman
