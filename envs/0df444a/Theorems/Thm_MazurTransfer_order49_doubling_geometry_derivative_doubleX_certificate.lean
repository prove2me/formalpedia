-- Prove2me | Theorems.Thm_MazurTransfer_order49_doubling_geometry_derivative_doubleX_certificate
-- name    : MazurTransfer.order49_doubling_geometry_derivative_doubleX_certificate
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-07T03:50:20.499995+00:00
-- url     : https://prove2.me/theorems/9c0813bf-f024-413b-b05f-a5f1e1214de6
-- title:
--   Exact polynomial certificate for the differentiated abscissa identity
-- statement:
--   For every rational family parameter $d$, the original composed abscissa polynomial equals the prescribed target doubling abscissa polynomial after substituting the seven original specialized coefficient functions and the source and quotient curves. The equality is an identity of polynomials, with every coefficient and normalization unchanged.
--
--   This exact certificate supports the original point-map doubling compatibility, then the exclusion of rational points of order $49$.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c; exact original _private.MazurTorsion.Kubert.OrderSevenIsogenyDoubling.0.MazurTorsion.Kubert.derivative_doubleX_certificate. Every original hypothesis is preserved at complete original Lean AST declaration ranges. The abscissa evaluation uses explicit simp rules to avoid imported auxiliary simp registrations; other original proof commands are retained. Thirty-one algebraic formula values, including private originals, were compared directly against original kernel constants by kernel-checked reflexivity. Uses the Proved original homogeneous polynomial aggregate and exact separately registered doubling helper contracts. Apache-2.0 headers and attribution retained. Named downstream consumers: original coordinate and point-map doubling compatibility, then full every-curve order49 exclusion.

import Mathlib
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49DoublingCoordinateFormulas
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
open Polynomial

theorem MazurTransfer.order49_doubling_geometry_derivative_doubleX_certificate (d : ℚ) :
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.composedVeluX
        (MazurTorsion.Kubert.orderSevenVeluA6 d) (MazurTorsion.Kubert.orderSevenVeluA5 d)
        (MazurTorsion.Kubert.orderSevenVeluA4 d) (MazurTorsion.Kubert.orderSevenVeluA3 d)
        (MazurTorsion.Kubert.orderSevenVeluA2 d) (MazurTorsion.Kubert.orderSevenVeluA1 d)
        (MazurTorsion.Kubert.orderSevenVeluA0 d) (MazurTorsion.Kubert.orderSevenFamily d) =
      MazurTorsion.Kubert.OrderSevenDoublingDerivative.targetDoubleX
        (MazurTorsion.Kubert.orderSevenQuotient d)
        (MazurTorsion.Kubert.orderSevenVeluA6 d) (MazurTorsion.Kubert.orderSevenVeluA5 d)
        (MazurTorsion.Kubert.orderSevenVeluA4 d) (MazurTorsion.Kubert.orderSevenVeluA3 d)
        (MazurTorsion.Kubert.orderSevenVeluA2 d) (MazurTorsion.Kubert.orderSevenVeluA1 d)
        (MazurTorsion.Kubert.orderSevenVeluA0 d) (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) := by sorry
