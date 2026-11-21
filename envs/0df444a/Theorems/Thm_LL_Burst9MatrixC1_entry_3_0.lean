-- Prove2me | Theorems.Thm_LL_Burst9MatrixC1_entry_3_0
-- name    : LL_Burst9MatrixC1.entry_3_0
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-21T05:02:41.687019+00:00
-- url     : https://prove2.me/theorems/f3a2ccdb-686a-4979-8a1f-ad70e9330da7
-- title:
--   Lower bound $a_{4,1}\ge 0.1549103$ for Wu's Section 7 matrix, $s=2.5$
-- statement:
--   The integral $\int_{1}^{2.2}\Xi_2(t;2.5,4.12,3.56,2.91,2.50)\,dt$, which is Wu's matrix entry $a_{4,1}$ and the entry in row 3, column 0 of integralMatrix, is at least $\frac{1549103}{10^7}=0.1549103$. Here $\Xi_2$ is the kernel of display 3.22 with $s=2.5$, $s'=4.12$, $\kappa_1=3.56$, $\kappa_2=2.91$, $\kappa_3=2.50$, and a numerical evaluation gives $0.1549103474$, a margin of about $4.7\times 10^{-8}$.
-- source:
--   J. Wu, Chen's double sieve, Goldbach's conjecture and the twin prime problem, Acta Arith. 114, 2004, 215-273, arXiv 0705.1652, display 7.1 on page 30 with the kernel of display 3.22, page 15

import Mathlib
import Definitions.Def_LL_Burst9MatrixC1_Params
import Definitions.Def_LL_Burst9MatrixC1_alpha
import Definitions.Def_LL_Burst9MatrixC1_ind
import Definitions.Def_LL_Burst9MatrixC1_sigma
import Definitions.Def_LL_Burst9MatrixC1_sigma0
import Definitions.Def_LL_Burst9MatrixC1_Xi1
import Definitions.Def_LL_Burst9MatrixC1_Xi2
import Definitions.Def_LL_Burst9MatrixC1_tableParams
import Definitions.Def_LL_Burst9MatrixC1_grid
import Definitions.Def_LL_Burst9MatrixC1_tableSp
import Definitions.Def_LL_Burst9MatrixC1_candidateMatrixQ
import Definitions.Def_LL_Burst9MatrixC1_tableKernel
import Definitions.Def_LL_Burst9MatrixC1_integralMatrix

open Real Set intervalIntegral Filter MeasureTheory
open scoped Topology

namespace LL_Burst9MatrixC1
theorem entry_3_0 : (candidateMatrixQ 3 0 : ℝ) ≤ integralMatrix 3 0 := by sorry
end LL_Burst9MatrixC1
