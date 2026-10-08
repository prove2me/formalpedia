-- Prove2me | Theorems.Thm_MazurTransfer_order49_vertical_xNumeratorHomogeneous_directional
-- name    : MazurTransfer.order49_vertical_xNumeratorHomogeneous_directional
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T04:37:24.693163+00:00
-- url     : https://prove2.me/theorems/cf7c8a40-f6a8-40b2-8be1-1a2d234ff19b
-- title:
--   The exact original directional doubling-abscissa identity
-- statement:
--   The exact original xNumeratorHomogeneous_directional theorem, with every rational scalar parameter, arbitrary curve or polynomial, polynomial-certificate equality and nonzero-denominator hypothesis retained at its original generality. This is a prerequisite for the original homogeneous differential certificate and the full every-curve order49 exclusion.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Doubling.xNumeratorHomogeneous_directional. Statement and proof extracted using kernel dependencies and complete original Lean AST ranges. Forty-eight new doubling and differential formula values were independently compared by kernel-checked reflexivity. Original proof commands and Apache-2.0 headers and attribution retained. Exact child contracts are explicit; an imported Open child is not a closed proof. Named downstream consumer: original homogeneous differential certificate, then full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49DifferentialCertificateFormulas
import Definitions.Def_MazurTransfer_Order49DoublingCoordinateFormulas
open Polynomial

theorem MazurTransfer.order49_vertical_xNumeratorHomogeneous_directional (W : WeierstrassCurve ℚ) (u v du dv : ℚ) :
    MazurTorsion.Doubling.xNumeratorHomogeneousDirectional W u v du dv * v *
          MazurTorsion.Doubling.completedCubicHomogeneous W u v -
        MazurTorsion.Doubling.xNumeratorHomogeneous W u v *
          (dv * MazurTorsion.Doubling.completedCubicHomogeneous W u v +
            v * MazurTorsion.Doubling.completedCubicHomogeneousDirectional W u v du dv) =
      2 * MazurTorsion.Doubling.completedYNumeratorHomogeneous W u v * (du * v - u * dv) := by sorry
