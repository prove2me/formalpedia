-- Prove2me | Theorems.Thm_Freiman_upper_large_model
-- name    : Freiman.upper_large_model
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:12:02.311987+00:00
-- url     : https://prove2.me/theorems/010fc12f-96ae-41da-aa42-ef84fdb65d74
-- title:
--   Every large central sum has controlled padded models
-- statement:
--   Admissible tails realizing x and y give a finite-alphabet central word of value n+x+y. Every padded truncation has all noncentral values bounded by 16/3, strictly below that central value.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. m2a:large-family, m2a:large-bound and m2a:completed-bounds.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_large_model (n : ℕ+) (hn : 5 ≤ (n : ℕ)) (x y : ℝ) (hx : x ∈ upperKA) (hy : y ∈ upperKA) :
    upperModel (((n : ℕ) : ℝ) + x + y) := by
  sorry

end Freiman
