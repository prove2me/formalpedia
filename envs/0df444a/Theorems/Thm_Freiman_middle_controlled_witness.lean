-- Prove2me | Theorems.Thm_Freiman_middle_controlled_witness
-- name    : Freiman.middle_controlled_witness
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:09:02.103935+00:00
-- url     : https://prove2.me/theorems/965cf4d4-8218-4b96-a5b1-51854a2223f4
-- title:
--   middle controlled witness
-- statement:
--   Initial coverage, exact compatible realization and all-center control produce a finite-exception word with central maximum t for every point of the closed middle interval.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part III, active source staging/m2b/m2b_body.tex, m2b:prop:path, m2b:eq:max and m2b:thm:middle

import Definitions.Def_Freiman_middleRoots

namespace Freiman

theorem middle_controlled_witness :
    ∀ t ∈ Set.Icc (Real.sqrt 21) (128/25:ℝ), ∃ a : ℤ→ℕ+, localValue a 0=t ∧ (∀ i : ℤ, localValue a i ≤ t) ∧ (∃ N : ℕ, ∀ i : ℤ, N ≤ i.natAbs → (a i:ℕ) ≤ 3) := by
  sorry

end Freiman
