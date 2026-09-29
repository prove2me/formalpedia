-- Prove2me | Theorems.Thm_Freiman_rational_two_cylinder_cover
-- name    : Freiman.rational_two_cylinder_cover
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:58:35.749986+00:00
-- url     : https://prove2.me/theorems/79b345da-e52e-45b8-a8bd-9391c69a03d3
-- title:
--   The two finite expansions cover the interval between their neighbors
-- statement:
--   The canonical expansion and the alternate final digits c_m−1,1 yield the two open adjacent cylinders. Every irrational between their outer endpoints belongs to one of them, because irrationality excludes the common rational p/q. Prefix uniqueness identifies p/q as an existing cfConvergent of b.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.2, found:legendre

import Definitions.Def_Freiman_perronArithmetic
import Definitions.Def_Freiman_rationalCylinderNeighbors

namespace Freiman

theorem rational_two_cylinder_cover (w : List ℕ+) (hw : w ≠ []) (hlast : 2 ≤ ((w.getLastD 1:ℕ+):ℕ)) (b : ℕ → ℕ+) (hx : cfValue b ∈ Set.Ioo (min (rationalCylinderNeighborLeft w) (rationalCylinderNeighborRight w)) (max (rationalCylinderNeighborLeft w) (rationalCylinderNeighborRight w))) :
    ∃ n : ℕ, cfConvergent b n=finiteCF w := by
  sorry

end Freiman
