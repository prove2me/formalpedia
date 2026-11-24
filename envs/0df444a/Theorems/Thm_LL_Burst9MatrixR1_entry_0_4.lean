-- Prove2me | Theorems.Thm_LL_Burst9MatrixR1_entry_0_4
-- name    : LL_Burst9MatrixR1.entry_0_4
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-21T04:30:24.295604+00:00
-- url     : https://prove2.me/theorems/440c99aa-e9ed-483a-a6a7-f7866bc72881
-- title:
--   Lower bound $a_{1,5}\ge 0.0271084$ for Wu's Section 7 matrix, $s=2.2$
-- statement:
--   The integral $\int_{2.5}^{2.6}\Xi_2(t;2.2,4.54,3.53,2.90,2.44)\,dt$, which is Wu's matrix entry $a_{1,5}$ and the entry in row 0, column 4 of integralMatrix, is at least $\frac{271084}{10^7}=0.0271084$. Here $\Xi_2$ is the kernel of display 3.22 with $s=2.2$, $s'=4.54$, $\kappa_1=3.53$, $\kappa_2=2.90$, $\kappa_3=2.44$, and a numerical evaluation gives $0.0271084782$, a margin of about $7.8\times 10^{-8}$.
-- source:
--   J. Wu, Chen's double sieve, Goldbach's conjecture and the twin prime problem, Acta Arith. 114, 2004, 215-273, arXiv 0705.1652, display 7.1 on page 30 with the kernel of display 3.22, page 15

import Mathlib
import Definitions.Def_LL_Burst9MatrixR1_Params
import Definitions.Def_LL_Burst9MatrixR1_alpha
import Definitions.Def_LL_Burst9MatrixR1_ind
import Definitions.Def_LL_Burst9MatrixR1_sigma
import Definitions.Def_LL_Burst9MatrixR1_sigma0
import Definitions.Def_LL_Burst9MatrixR1_Xi1
import Definitions.Def_LL_Burst9MatrixR1_Xi2
import Definitions.Def_LL_Burst9MatrixR1_tableParams
import Definitions.Def_LL_Burst9MatrixR1_grid
import Definitions.Def_LL_Burst9MatrixR1_tableSp
import Definitions.Def_LL_Burst9MatrixR1_candidateMatrixQ
import Definitions.Def_LL_Burst9MatrixR1_tableKernel
import Definitions.Def_LL_Burst9MatrixR1_integralMatrix

open Real Set intervalIntegral Filter MeasureTheory
open scoped Topology

namespace LL_Burst9MatrixR1
theorem entry_0_4 : (candidateMatrixQ 0 4 : ℝ) ≤ integralMatrix 0 4 := by sorry
end LL_Burst9MatrixR1
