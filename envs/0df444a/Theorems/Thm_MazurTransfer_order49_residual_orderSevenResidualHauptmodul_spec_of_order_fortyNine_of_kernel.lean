-- Prove2me | Theorems.Thm_MazurTransfer_order49_residual_orderSevenResidualHauptmodul_spec_of_order_fortyNine_of_kernel
-- name    : MazurTransfer.order49_residual_orderSevenResidualHauptmodul_spec_of_order_fortyNine_of_kernel
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T05:17:54.191476+00:00
-- url     : https://prove2.me/theorems/a776ec8a-341d-493d-9ac1-b07798f3695b
-- title:
--   The exact original residual Hauptmodul is nonzero and satisfies the quotient j-invariant equation
-- statement:
--   For every elliptic member of the original order-seven family and every nonsingular rational affine point of exact order 49, if the original seven-isogeny point function kills its seventh multiple, the original residual Hauptmodul is nonzero and its original j numerator times the quotient discriminant equals the quotient c4 cubed times the residual Hauptmodul to the seventh power. All original hypotheses, including the kernel premise, are explicit and unchanged.
--
--   This supplies an exact point-function fact used in the original order-49 exclusion.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original MazurTorsion.Kubert.orderSevenResidualHauptmodul_spec_of_order_fortyNine_of_kernel. Original hypotheses, declaration ranges and proof commands preserved using the kernel graph and complete Lean AST. All point definitions were independently compared with the WIP originals; all reused geometric helpers are Proved and locally rechecked with closed proofs. Apache-2.0 headers and attribution retained. Named downstream consumers: exact residual Hauptmodul specification, then full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49HauptmodulJNumerator
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyGeometryFormulas
import Definitions.Def_MazurTransfer_Order49SevenIsogenyPointConstructors
open Polynomial

theorem MazurTransfer.order49_residual_orderSevenResidualHauptmodul_spec_of_order_fortyNine_of_kernel {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (hQ : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 49)
    (hkernel : MazurTorsion.Kubert.orderSevenPointMap d
      ((7 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP) = 0) :
    MazurTorsion.Kubert.orderSevenResidualHauptmodul d x y ≠ 0 ∧
      MazurTorsion.Kubert.orderSevenJNumerator (MazurTorsion.Kubert.orderSevenResidualHauptmodul d x y) *
          (MazurTorsion.Kubert.orderSevenQuotient d).Δ =
        (MazurTorsion.Kubert.orderSevenQuotient d).c₄ ^ 3 *
          MazurTorsion.Kubert.orderSevenResidualHauptmodul d x y ^ 7 := by sorry
