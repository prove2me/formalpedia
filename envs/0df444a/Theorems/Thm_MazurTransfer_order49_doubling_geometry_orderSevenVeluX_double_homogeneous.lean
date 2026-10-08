-- Prove2me | Theorems.Thm_MazurTransfer_order49_doubling_geometry_orderSevenVeluX_double_homogeneous
-- name    : MazurTransfer.order49_doubling_geometry_orderSevenVeluX_double_homogeneous
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T03:50:32.314899+00:00
-- url     : https://prove2.me/theorems/4810561a-fb46-4253-8132-df131741d575
-- title:
--   Homogeneous abscissa compatibility of the seven-isogeny and doubling
-- statement:
--   For every rational $d,x$, the original homogeneous numerator of the seven-isogeny abscissa, evaluated at the source doubling numerators, equals the original quotient doubling numerator evaluated at the isogeny numerator and the square of its kernel polynomial. This identity has no denominator nonvanishing hypothesis.
--
--   This exact certificate supports the original point-map doubling compatibility, then the exclusion of rational points of order $49$.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original _private.MazurTorsion.Kubert.OrderSevenIsogenyDoubling.0.MazurTorsion.Kubert.orderSevenVeluX_double_homogeneous. Every original hypothesis is preserved at complete original Lean AST declaration ranges. The abscissa evaluation uses explicit simp rules to avoid imported auxiliary simp registrations; other original proof commands are retained. Thirty-one algebraic formula values, including private originals, were compared directly against original kernel constants by kernel-checked reflexivity. Uses the Proved original homogeneous polynomial aggregate and exact separately registered doubling helper contracts. Apache-2.0 headers and attribution retained. Named downstream consumers: original coordinate and point-map doubling compatibility, then full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49DoublingCoordinateFormulas
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyGeometryFormulas
open Polynomial

theorem MazurTransfer.order49_doubling_geometry_orderSevenVeluX_double_homogeneous (d x : ℚ) :
    MazurTorsion.Kubert.orderSevenVeluXNumeratorHomogeneous d
        (MazurTorsion.Doubling.xNumerator (MazurTorsion.Kubert.orderSevenFamily d) x)
        (MazurTorsion.Doubling.completedCubic (MazurTorsion.Kubert.orderSevenFamily d) x) =
      MazurTorsion.Doubling.xNumeratorHomogeneous (MazurTorsion.Kubert.orderSevenQuotient d)
        (MazurTorsion.Kubert.orderSevenVeluXNumerator d x)
        (MazurTorsion.Kubert.orderSevenKernelPolynomial d x ^ 2) := by sorry
