-- Prove2me | Theorems.Thm_Freiman_upper_small_data
-- name    : Freiman.upper_small_data
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:12:04.790588+00:00
-- url     : https://prove2.me/theorems/4e70f006-1aba-4595-993c-28ac74586e81
-- title:
--   Alphabet and central value of the 1,4,1 family
-- statement:
--   The fixed central block 1,4,1 with its two B-state tails uses digits at most 4 and has central value 4+1/(1+x)+1/(1+y), where x and y are the existing cfValue tails.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. m2a:small-family.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_small_data (l r : ℕ → ℕ+) (hl : upperAdmissible l) (hl0 : (l 0 : ℕ) ≤ 3) (hr : upperAdmissible r) (hr0 : (r 0 : ℕ) ≤ 3) :
    (∀ i, (upperCentral 4 (upperOne l) (upperOne r) i : ℕ) ≤ 4) ∧
    localValue (upperCentral 4 (upperOne l) (upperOne r)) 0 = 4 + 1 / (1 + cfValue l) + 1 / (1 + cfValue r) := by
  sorry

end Freiman
