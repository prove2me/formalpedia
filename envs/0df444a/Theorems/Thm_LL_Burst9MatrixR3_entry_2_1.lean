-- Prove2me | Theorems.Thm_LL_Burst9MatrixR3_entry_2_1
-- name    : LL_Burst9MatrixR3.entry_2_1
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-21T04:50:21.914098+00:00
-- url     : https://prove2.me/theorems/9bb2010a-f315-45b3-863f-b9fe5b20da35
-- title:
--   Lower bound $a_{3,2}\ge 0.0250515$ for Wu's Section 7 matrix, $s=2.4$
-- statement:
--   The integral $\int_{2.2}^{2.3}\Xi_2(t;2.4,4.46,3.57,2.87,2.40)\,dt$, which is Wu's matrix entry $a_{3,2}$ and the entry in row 2, column 1 of integralMatrix, is at least $\frac{250515}{10^7}=0.0250515$. Here $\Xi_2$ is the kernel of display 3.22 with $s=2.4$, $s'=4.46$, $\kappa_1=3.57$, $\kappa_2=2.87$, $\kappa_3=2.40$, and a numerical evaluation gives $0.0250515037$, a margin of about $3.7\times 10^{-9}$.
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
theorem entry_2_1 : (candidateMatrixQ 2 1 : ℝ) ≤ integralMatrix 2 1 := by sorry
end LL_Burst9MatrixR3
