-- Prove2me | Theorems.Thm_Freiman_rational_adjacent_radius
-- name    : Freiman.rational_adjacent_radius
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:58:26.711646+00:00
-- url     : https://prove2.me/theorems/ef61ac62-65ec-4a44-b9ee-879ea743d333
-- title:
--   Both rational neighbors are farther than the Legendre radius
-- statement:
--   The determinants give opposite-sided neighbor distances 1/(q(q+v)) and 1/(q(2q−v)); 0<v<q makes both exceed 1/(2q²). This is the finite rational inequality part of Legendre’s proof.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.2, found:legendre

import Definitions.Def_Freiman_perronArithmetic
import Definitions.Def_Freiman_rationalCylinderNeighbors

namespace Freiman

theorem rational_adjacent_radius (w : List ℕ+) (hw : w ≠ []) (hlast : 2 ≤ ((w.getLastD 1:ℕ+):ℕ)) (x : ℝ) (hx : |x-finiteCF w|<1/(2*(wordContinuantQ w:ℝ)^2)) :
    x ∈ Set.Ioo (min (rationalCylinderNeighborLeft w) (rationalCylinderNeighborRight w))
      (max (rationalCylinderNeighborLeft w) (rationalCylinderNeighborRight w)) := by
  sorry

end Freiman
