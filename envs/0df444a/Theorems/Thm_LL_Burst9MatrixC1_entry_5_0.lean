-- Prove2me | Theorems.Thm_LL_Burst9MatrixC1_entry_5_0
-- name    : LL_Burst9MatrixC1.entry_5_0
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-21T05:01:51.667719+00:00
-- url     : https://prove2.me/theorems/c2adf212-9a24-4a51-a0e0-76c2fe6b60a5
-- title:
--   Lower bound $a_{6,1}\ge 0.1602317$ for Wu's Section 7 matrix, $s=2.7$
-- statement:
--   The integral $\int_{1}^{2.2}\Xi_1(t;2.7,3.47)\,dt$, which is Wu's matrix entry $a_{6,1}$ and the entry in row 5, column 0 of integralMatrix, is at least $\frac{1602317}{10^7}=0.1602317$. Here $\Xi_1$ is the kernel of display 3.21 with $s=2.7$, $s'=3.47$, and a numerical evaluation gives $0.1602317488$, a margin of about $4.9\times 10^{-8}$.
-- source:
--   J. Wu, Chen's double sieve, Goldbach's conjecture and the twin prime problem, Acta Arith. 114, 2004, 215-273, arXiv 0705.1652, display 7.2 on page 30 with the kernel of display 3.21, page 14

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
theorem entry_5_0 : (candidateMatrixQ 5 0 : ℝ) ≤ integralMatrix 5 0 := by sorry
end LL_Burst9MatrixC1
