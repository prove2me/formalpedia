-- Prove2me | Theorems.Thm_MazurTransfer_order49_vertical_veluXHomogeneous_directional
-- name    : MazurTransfer.order49_vertical_veluXHomogeneous_directional
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T04:37:05.90642+00:00
-- url     : https://prove2.me/theorems/f953d368-f69c-4d39-bd6b-420776777481
-- title:
--   The exact original directional seven-isogeny abscissa identity
-- statement:
--   The exact original veluXHomogeneous_directional theorem, with every rational scalar parameter, arbitrary curve or polynomial, polynomial-certificate equality and nonzero-denominator hypothesis retained at its original generality. This is a prerequisite for the original homogeneous differential certificate and the full every-curve order49 exclusion.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXHomogeneous_directional. Statement and proof extracted using kernel dependencies and complete original Lean AST ranges. Forty-eight new doubling and differential formula values were independently compared by kernel-checked reflexivity. Original proof commands and Apache-2.0 headers and attribution retained. Exact child contracts are explicit; an imported Open child is not a closed proof. Named downstream consumer: original homogeneous differential certificate, then full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49DifferentialCertificateFormulas
open Polynomial

theorem MazurTransfer.order49_vertical_veluXHomogeneous_directional (a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c u v du dv : ℚ) :
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXHomogeneousDirectional a₆ a₅ a₄ a₃ a₂ a₁ a₀
          u v du dv * v * MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelHomogeneous b c u v -
        MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXHomogeneous a₆ a₅ a₄ a₃ a₂ a₁ a₀ u v *
          (dv * MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelHomogeneous b c u v +
            2 * v * MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelHomogeneousDirectional b c u v du dv) =
      MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluDifferentialHomogeneous a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c u v *
        (du * v - u * dv) := by sorry
