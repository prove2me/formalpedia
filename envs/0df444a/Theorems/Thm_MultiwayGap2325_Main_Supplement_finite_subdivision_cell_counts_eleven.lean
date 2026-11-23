-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_Supplement_finite_subdivision_cell_counts_eleven
-- name    : MultiwayGap2325.Main.Supplement.finite_subdivision_cell_counts_eleven
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:20:15.725522+00:00
-- url     : https://prove2.me/theorems/fd8c412a-cb8e-4985-b686-2e445f6d10b7
-- title:
--   The §7.6 ordered regions have exactly 2,937 computed cells
-- statement:
--   For the parameters of Proposition 3.6, $q=11$, $T=249/400$, $n=3$, and $r_0=5$, direct evaluation of the exact rational subdivision of Section 7.2 gives the cell counts
--   $$
--   (3,18,81,324,351,378,405,432,459,486)
--   $$
--   in dimensions $r=2,\ldots,11$, respectively. In particular, the ordered regions contain exactly
--   $$
--   3+18+81+324+351+378+405+432+459+486=2937
--   $$
--   cells. This verifies the finite geometry underlying the external integer table before any flow or capacity data are supplied.
-- source:
--   Dimitar Chakarov and Yury Makarychev, STOC 2027 submission #697, §7.6, p.31 (cell-count table and total), using the subdivision defined in §7.2, pp.26–27.

import Definitions.Def_MultiwayGap2325_Main_Supplement_FiniteSubdivision

/-- The exact rational mesh for Proposition 3.6 has the cell counts printed in §7.6. -/
theorem MultiwayGap2325.Main.Supplement.finite_subdivision_cell_counts_eleven :
    MultiwayGap2325.Main.Supplement.orderedRegionCellCounts 11 (249 / 400) 3 5 =
      [3, 18, 81, 324, 351, 378, 405, 432, 459, 486] ∧
    (MultiwayGap2325.Main.Supplement.orderedRegionCells 11 (249 / 400) 3 5).length = 2937 := by sorry
