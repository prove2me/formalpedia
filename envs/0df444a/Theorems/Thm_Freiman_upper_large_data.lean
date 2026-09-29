-- Prove2me | Theorems.Thm_Freiman_upper_large_data
-- name    : Freiman.upper_large_data
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:12:04.212309+00:00
-- url     : https://prove2.me/theorems/00212d96-7970-4cc0-956f-ef48e35d2643
-- title:
--   Alphabet and central value of the large family
-- statement:
--   The central word with digit n≥5 and two admissible outward tails uses digits at most n, and its local value at zero is n plus the two existing cfValue tails.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. m2a:large-family.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_large_data (n : ℕ+) (hn : 5 ≤ (n : ℕ)) (l r : ℕ → ℕ+) (hl : upperAdmissible l) (hr : upperAdmissible r) :
    (∀ i, (upperCentral n l r i : ℕ) ≤ (n : ℕ)) ∧
    localValue (upperCentral n l r) 0 = ((n : ℕ) : ℝ) + cfValue l + cfValue r := by
  sorry

end Freiman
