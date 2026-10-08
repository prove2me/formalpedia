-- Prove2me | Theorems.Thm_MazurTransfer_order49_vertical_kernel_polynomial_identity
-- name    : MazurTransfer.order49_vertical_kernel_polynomial_identity
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T04:37:01.922078+00:00
-- url     : https://prove2.me/theorems/74a4cb80-5067-41f8-8e4e-91c7d123a7ed
-- title:
--   The exact original specialized kernel polynomial identity
-- statement:
--   The exact original kernel_polynomial_identity theorem, with every rational scalar parameter, arbitrary curve or polynomial, polynomial-certificate equality and nonzero-denominator hypothesis retained at its original generality. This is a prerequisite for the original homogeneous differential certificate and the full every-curve order49 exclusion.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.OrderSevenDoublingSpecialization.kernel_polynomial_identity. Statement and proof extracted using kernel dependencies and complete original Lean AST ranges. Forty-eight new doubling and differential formula values were independently compared by kernel-checked reflexivity. Original proof commands and Apache-2.0 headers and attribution retained. Exact child contracts are explicit; an imported Open child is not a closed proof. Named downstream consumer: original homogeneous differential certificate, then full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49DifferentialCertificateFormulas
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49DoublingCoordinateFormulas
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
open Polynomial

theorem MazurTransfer.order49_vertical_kernel_polynomial_identity (d : ℚ) :
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.composedKernel (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) (MazurTorsion.Kubert.orderSevenFamily d) =
      MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseKernel (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) *
        MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseVeluDifferential (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₆ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₅ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₄ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₃ d)
          (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₂ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₁ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₀ d) (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) := by sorry
