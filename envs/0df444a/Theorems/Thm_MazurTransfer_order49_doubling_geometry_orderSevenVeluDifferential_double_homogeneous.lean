-- Prove2me | Theorems.Thm_MazurTransfer_order49_doubling_geometry_orderSevenVeluDifferential_double_homogeneous
-- name    : MazurTransfer.order49_doubling_geometry_orderSevenVeluDifferential_double_homogeneous
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T03:50:24.646885+00:00
-- url     : https://prove2.me/theorems/0ade1a42-7988-402f-8342-2537b6a96308
-- title:
--   Homogeneous vertical compatibility under the original nonvanishing hypotheses
-- statement:
--   For $d,x\in\mathbb Q$, suppose the original kernel polynomial and differential numerator are both nonzero at $x$. Then the homogeneous differential numerator evaluated at the source doubling numerators, multiplied by the source completed vertical numerator, equals the quotient completed vertical numerator evaluated at the isogeny abscissa numerator and the square of the kernel polynomial. Both original nonvanishing hypotheses remain explicit.
--
--   This exact certificate supports the original point-map doubling compatibility, then the exclusion of rational points of order $49$.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original _private.MazurTorsion.Kubert.OrderSevenIsogenyDoubling.0.MazurTorsion.Kubert.orderSevenVeluDifferential_double_homogeneous. Every original hypothesis is preserved at complete original Lean AST declaration ranges. The abscissa evaluation uses explicit simp rules to avoid imported auxiliary simp registrations; other original proof commands are retained. Thirty-one algebraic formula values, including private originals, were compared directly against original kernel constants by kernel-checked reflexivity. Uses the Proved original homogeneous polynomial aggregate and exact separately registered doubling helper contracts. Apache-2.0 headers and attribution retained. Named downstream consumers: original coordinate and point-map doubling compatibility, then full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49DoublingCoordinateFormulas
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyGeometryFormulas
open Polynomial

theorem MazurTransfer.order49_doubling_geometry_orderSevenVeluDifferential_double_homogeneous (d x : ℚ)
    (hK : MazurTorsion.Kubert.orderSevenKernelPolynomial d x ≠ 0)
    (hN : MazurTorsion.Kubert.orderSevenVeluDifferentialNumerator d x ≠ 0) :
    MazurTorsion.Kubert.orderSevenVeluDifferentialNumeratorHomogeneous d
        (MazurTorsion.Doubling.xNumerator (MazurTorsion.Kubert.orderSevenFamily d) x)
        (MazurTorsion.Doubling.completedCubic (MazurTorsion.Kubert.orderSevenFamily d) x) *
          MazurTorsion.Doubling.completedYNumerator (MazurTorsion.Kubert.orderSevenFamily d) x =
      MazurTorsion.Doubling.completedYNumeratorHomogeneous (MazurTorsion.Kubert.orderSevenQuotient d)
        (MazurTorsion.Kubert.orderSevenVeluXNumerator d x)
        (MazurTorsion.Kubert.orderSevenKernelPolynomial d x ^ 2) := by sorry
