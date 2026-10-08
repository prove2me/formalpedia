-- Prove2me | Theorems.Thm_MazurTransfer_order18_coefficient_hensel_root_exists
-- name    : MazurTransfer.order18_coefficient_hensel_root_exists
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T17:54:38.951205+00:00
-- url     : https://prove2.me/theorems/a5f97b01-f720-4f0d-bd60-70a86ffa6c8c
-- title:
--   Order18: the selected simple cubic root lifts in the actual dyadic completion
-- statement:
--   Let \(\widehat K\) be the published completion of the real cubic coefficient field at its exact prime above \(2\), and let \(\widehat{\mathcal O}_K\) be its completion-integer ring. There exists \(\rho\in\widehat{\mathcal O}_K\) such that \[\rho^3-3\rho-10=0,\qquad \rho\in\mathfrak m,\] where \(\mathfrak m\) is the maximal ideal. This certifies existence of the selected lift of the simple residue root zero; all local point-image and squareclass-separation conclusions remain separate obligations.
-- source:
--   User WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Exact original exists_localTwoDivisionRoot_aux closure selected by typed kernel dependencies and whole original Lean AST commands. Actual full ring-of-integers prime and coefficient completion are defined separately using the Proved Kummer–Dedekind arithmetic certificate. Original Apache-2.0 headers and attribution retained. This witness is a separate arithmetic theorem before constructing the local root and algebra projection as pure data. Named downstream consumers: the two smaller arithmetic halves of the unchanged order18 local mask exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order18CoefficientCompletionData

theorem MazurTransfer.order18_coefficient_hensel_root_exists :
    ∃ r : MazurTorsion.XOneEighteenDyadicCompletionBridge.CoefficientCompletionIntegers,
      MazurTorsion.XOneEighteenDyadicCompletionBridge.localTwoDivisionPolynomial.IsRoot r ∧
        r ∈ IsLocalRing.maximalIdeal MazurTorsion.XOneEighteenDyadicCompletionBridge.CoefficientCompletionIntegers := by sorry
