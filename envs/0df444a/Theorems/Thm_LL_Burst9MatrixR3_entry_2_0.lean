-- Prove2me | Theorems.Thm_LL_Burst9MatrixR3_entry_2_0
-- name    : LL_Burst9MatrixR3.entry_2_0
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-21T04:53:44.05414+00:00
-- url     : https://prove2.me/theorems/b5fc9b82-e7f9-41df-b71b-979b15418d94
-- title:
--   Lower bound $a_{3,1}\ge 0.1525199$ for Wu's Section 7 matrix, $s=2.4$
-- statement:
--   The integral $\int_{1}^{2.2}\Xi_2(t;2.4,4.46,3.57,2.87,2.40)\,dt$, which is Wu's matrix entry $a_{3,1}$ and the entry in row 2, column 0 of integralMatrix, is at least $\frac{1525199}{10^7}=0.1525199$. Here $\Xi_2$ is the kernel of display 3.22 with $s=2.4$, $s'=4.46$, $\kappa_1=3.57$, $\kappa_2=2.87$, $\kappa_3=2.40$, and a numerical evaluation gives $0.1525199200$, a margin of about $2.0\times 10^{-8}$.
-- source:
--   J. Wu, Chen's double sieve, Goldbach's conjecture and the twin prime problem, Acta Arith. 114, 2004, 215-273, arXiv 0705.1652, display 7.1 on page 30 with the kernel of display 3.22, page 15

import Mathlib
import Definitions.Def_LL_Burst9MatrixR3_Params
import Definitions.Def_LL_Burst9MatrixR3_alpha
import Definitions.Def_LL_Burst9MatrixR3_ind
import Definitions.Def_LL_Burst9MatrixR3_sigma
import Definitions.Def_LL_Burst9MatrixR3_sigma0
import Definitions.Def_LL_Burst9MatrixR3_Xi1
import Definitions.Def_LL_Burst9MatrixR3_Xi2
import Definitions.Def_LL_Burst9MatrixR3_tableParams
import Definitions.Def_LL_Burst9MatrixR3_grid
import Definitions.Def_LL_Burst9MatrixR3_tableSp
import Definitions.Def_LL_Burst9MatrixR3_candidateMatrixQ
import Definitions.Def_LL_Burst9MatrixR3_tableKernel
import Definitions.Def_LL_Burst9MatrixR3_integralMatrix

open Real Set intervalIntegral Filter MeasureTheory
open scoped Topology

namespace LL_Burst9MatrixR3
theorem entry_2_0 : (candidateMatrixQ 2 0 : ℝ) ≤ integralMatrix 2 0 := by sorry
end LL_Burst9MatrixR3
