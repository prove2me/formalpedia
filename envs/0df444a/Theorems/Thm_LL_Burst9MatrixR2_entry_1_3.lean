-- Prove2me | Theorems.Thm_LL_Burst9MatrixR2_entry_1_3
-- name    : LL_Burst9MatrixR2.entry_1_3
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-21T04:42:33.155806+00:00
-- url     : https://prove2.me/theorems/a16791b3-0af9-4c93-ab51-f5f9d3f8e2ec
-- title:
--   Lower bound $a_{2,4}\ge 0.0262914$ for Wu's Section 7 matrix, $s=2.3$
-- statement:
--   The integral $\int_{2.4}^{2.5}\Xi_2(t;2.3,4.50,3.54,2.88,2.43)\,dt$, which is Wu's matrix entry $a_{2,4}$ and the entry in row 1, column 3 of integralMatrix, is at least $\frac{262914}{10^7}=0.0262914$. Here $\Xi_2$ is the kernel of display 3.22 with $s=2.3$, $s'=4.50$, $\kappa_1=3.54$, $\kappa_2=2.88$, $\kappa_3=2.43$, and a numerical evaluation gives $0.0262914366$, a margin of about $3.7\times 10^{-8}$.
-- source:
--   J. Wu, Chen's double sieve, Goldbach's conjecture and the twin prime problem, Acta Arith. 114, 2004, 215-273, arXiv 0705.1652, display 7.1 on page 30 with the kernel of display 3.22, page 15

import Mathlib
import Definitions.Def_LL_Burst9MatrixR2_Params
import Definitions.Def_LL_Burst9MatrixR2_alpha
import Definitions.Def_LL_Burst9MatrixR2_ind
import Definitions.Def_LL_Burst9MatrixR2_sigma
import Definitions.Def_LL_Burst9MatrixR2_sigma0
import Definitions.Def_LL_Burst9MatrixR2_Xi1
import Definitions.Def_LL_Burst9MatrixR2_Xi2
import Definitions.Def_LL_Burst9MatrixR2_tableParams
import Definitions.Def_LL_Burst9MatrixR2_grid
import Definitions.Def_LL_Burst9MatrixR2_tableSp
import Definitions.Def_LL_Burst9MatrixR2_candidateMatrixQ
import Definitions.Def_LL_Burst9MatrixR2_tableKernel
import Definitions.Def_LL_Burst9MatrixR2_integralMatrix

open Real Set intervalIntegral Filter MeasureTheory
open scoped Topology

namespace LL_Burst9MatrixR2
theorem entry_1_3 : (candidateMatrixQ 1 3 : ℝ) ≤ integralMatrix 1 3 := by sorry
end LL_Burst9MatrixR2
