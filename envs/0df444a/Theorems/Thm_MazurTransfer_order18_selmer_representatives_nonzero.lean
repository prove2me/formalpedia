-- Prove2me | Theorems.Thm_MazurTransfer_order18_selmer_representatives_nonzero
-- name    : MazurTransfer.order18_selmer_representatives_nonzero
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T18:36:45.448041+00:00
-- url     : https://prove2.me/theorems/327da6b1-3d90-4de9-b7b6-4e8fed6b9bc1
-- title:
--   Order-18 explicit Selmer representatives are all nonzero
-- statement:
--   In the separately constructed degree-nine field $M$, all six original explicit representatives are nonzero:
--   \[\alpha,\beta,h_1,h_2,h_3,h_4\ne0.\]
--   The proof uses their exact relative norms and the coefficient root’s cubic relation. This is only constructor validity for the corresponding unit square classes. It asserts no support membership, norm-kernel membership, independence, Selmer cardinality or torsion exclusion. Named downstream consumers: the exact global Selmer ambient-data interface and the two-prime valuation certificate.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c. All six original nonzero proofs selected by kernel dependencies and complete resolved Lean AST commands, with separately Proved field-validity contracts. Original Apache-2.0 headers and authors retained.

import Definitions.Def_MazurTransfer_Order18CompositumField

theorem MazurTransfer.order18_selmer_representatives_nonzero :
MazurTorsion.XOneEighteenTwoDivisionArithmetic.alpha ≠ 0 ∧
  MazurTorsion.XOneEighteenTwoDivisionArithmetic.beta ≠ 0 ∧
  MazurTorsion.XOneEighteenTwoDivisionArithmetic.h1 ≠ 0 ∧
  MazurTorsion.XOneEighteenTwoDivisionArithmetic.h2 ≠ 0 ∧
  MazurTorsion.XOneEighteenTwoDivisionArithmetic.h3 ≠ 0 ∧
  MazurTorsion.XOneEighteenTwoDivisionArithmetic.h4 ≠ 0 := by sorry
