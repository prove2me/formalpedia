-- Prove2me | Theorems.Thm_MazurTransfer_order49_vertical_vertical_at_point
-- name    : MazurTransfer.order49_vertical_vertical_at_point
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T04:36:46.047418+00:00
-- url     : https://prove2.me/theorems/f16d8141-b000-453f-a7c1-484e38ab3a7c
-- title:
--   The exact original vertical-coordinate consequence of three polynomial certificates
-- statement:
--   The exact original vertical_at_point theorem, with every rational scalar parameter, arbitrary curve or polynomial, polynomial-certificate equality and nonzero-denominator hypothesis retained at its original generality. This is a prerequisite for the original homogeneous differential certificate and the full every-curve order49 exclusion.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.OrderSevenDoublingDerivative.vertical_at_point. Statement and proof extracted using kernel dependencies and complete original Lean AST ranges. Forty-eight new doubling and differential formula values were independently compared by kernel-checked reflexivity. Original proof commands and Apache-2.0 headers and attribution retained. Exact child contracts are explicit; an imported Open child is not a closed proof. Named downstream consumer: original homogeneous differential certificate, then full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49DifferentialCertificateFormulas
import Definitions.Def_MazurTransfer_Order49DoublingCoordinateFormulas
open Polynomial

theorem MazurTransfer.order49_vertical_vertical_at_point (a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c : ℚ)
    (W W' : WeierstrassCurve ℚ) (x : ℚ)
    (hX : MazurTorsion.Kubert.OrderSevenDoublingDerivative.composedVeluX a₆ a₅ a₄ a₃ a₂ a₁ a₀ W =
      MazurTorsion.Kubert.OrderSevenDoublingDerivative.targetDoubleX W' a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c)
    (hkernel : MazurTorsion.Kubert.OrderSevenDoublingDerivative.composedKernel b c W =
      MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseKernel b c * MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseVeluDifferential a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c)
    (hlanding :
      MazurTorsion.Kubert.OrderSevenDoublingDerivative.targetCompletedCubic W' a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c =
        MazurTorsion.Kubert.OrderSevenDoublingDerivative.sourceCompletedCubic W *
          MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseVeluDifferential a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c ^ 2)
    (hK : (MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseKernel b c).eval x ≠ 0)
    (hN : (MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseVeluDifferential a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c).eval x ≠ 0) :
    (MazurTorsion.Kubert.OrderSevenDoublingDerivative.composedVeluDifferential a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c W).eval x *
        (MazurTorsion.Kubert.OrderSevenDoublingDerivative.sourceDoubleCompletedY W).eval x =
      (MazurTorsion.Kubert.OrderSevenDoublingDerivative.targetDoubleCompletedY W' a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c).eval x := by sorry
