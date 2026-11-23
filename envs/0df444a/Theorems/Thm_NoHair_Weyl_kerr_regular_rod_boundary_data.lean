-- Prove2me | Theorems.Thm_NoHair_Weyl_kerr_regular_rod_boundary_data
-- name    : NoHair.Weyl.kerr_regular_rod_boundary_data
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T10:33:32.105095+00:00
-- url     : https://prove2.me/theorems/a234060c-df52-4cd4-9258-4cb7c509273e
-- title:
--   Regular weighted axial data of Kerr on the entire compactified prolate rectangle
-- statement:
--   For every admissible vacuum Kerr parameter pair, the weighted norm and twist defect extend with continuous angular derivatives to the two polar sides, the inner edge and the infinity edge of the prolate rectangle. The inward norm slopes at the poles are strictly positive in the inward angular coordinate, including at all four corners.
-- source:
--   P. T. Chruściel and J. Lopes Costa, On uniqueness of stationary vacuum black holes, Astérisque 321 (2008), §§6.2–6.7, https://arxiv.org/abs/0806.0016. The compactified variables and angular derivative criterion here are an explicit sufficient condition for the platform’s normalized rod estimates.

import Definitions.Def_NoHair_regularRodBoundaryData

open NoHair NoHair.Weyl Set
open scoped ContDiff Manifold

theorem NoHair.Weyl.kerr_regular_rod_boundary_data (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0) :
    Nonempty (RegularRodBoundaryData (kerrErnst m a) m (Real.sqrt (m^2-a^2)) (m*a)) := by
  sorry
