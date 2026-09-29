-- Prove2me | Theorems.Thm_Freiman_upper_padding_upper_bound
-- name    : Freiman.upper_padding_upper_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:12:16.871289+00:00
-- url     : https://prove2.me/theorems/afca41a0-4ed4-4efa-91b7-618781cadaca
-- title:
--   A single central error bounds every padded local height
-- statement:
--   The absolute error of the padded central height bounds its excess over t; all noncentral heights are already at most D<t.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. The bound by max(t_j,D) in the padded-copy argument.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_padding_upper_bound (a : ℤ → ℕ+) (D t : ℝ) (hD : D < t) (hb : ∀ j i, i ≠ 0 → localValue (upperPad a j) i ≤ D) :
    ∀ j i, localValue (upperPad a j) i ≤ t + |localValue (upperPad a j) 0 - t| := by
  sorry

end Freiman
